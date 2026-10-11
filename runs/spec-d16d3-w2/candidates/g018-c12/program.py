import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Moore bound and projective-plane arc helpers (D = 3 arc-extended PG(2,q))
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _pg_incidence(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points 0..m-1, lines indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Incidence graph of PG(2,q) plus, per element of S, an A-vertex and a B-vertex."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _arc_candidates(d, deadline, rng):
    """For each prime power q with q + 1 <= d, build the best arc-extended PG(2,q) graph."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points = _pg_incidence(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 60, deadline))
        if s >= 2:
            cs = _conic_set(q, index)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Haar graphs from difference covers, searched by a tabu / WalkSAT-style walk.
#
# H(m, S) with |S| = k is k-regular bipartite, and has diameter 3 exactly
# when S - S = Z_m (a difference cover). Order 2m, with m <= k(k-1)+1.
#
# New helper: _cover_walk. It keeps an incremental count of how many ordered
# pairs realise each difference. Each step picks a random uncovered difference g
# and proposes new elements y = s +- g, which would cover g. It then does the
# best (x, y) swap under a short tabu memory. _bump updates the counts and
# returns the change in the number of uncovered differences, so a swap is
# evaluated and undone in O(k) without rebuilding anything.
# ----------------------------------------------------------------------------

def _bump(cnt, others, x, m, sign):
    """Add (sign=+1) or remove (sign=-1) the differences between x and each element of others.

    Returns the change in the number of uncovered differences (cnt == 0, g != 0).
    """
    ch = 0
    for s in others:
        g = (x - s) % m
        c = cnt[g]
        if sign > 0:
            if c == 0:
                ch -= 1
            cnt[g] = c + 1
        else:
            c -= 1
            cnt[g] = c
            if c == 0:
                ch += 1
        g = (s - x) % m
        c = cnt[g]
        if sign > 0:
            if c == 0:
                ch -= 1
            cnt[g] = c + 1
        else:
            c -= 1
            cnt[g] = c
            if c == 0:
                ch += 1
    return ch


def _cover_walk(k, m, rng, deadline):
    """Find S subset of Z_m with |S| = k and S - S = Z_m. Returns sorted S, or None on timeout."""
    if m < k:
        return None
    tenure_base = 3
    while time.monotonic() < deadline:
        S = rng.sample(range(m), k)
        inS = set(S)
        cnt = [0] * m
        for a in S:
            for b in S:
                if a != b:
                    cnt[(a - b) % m] += 1
        U = sum(1 for g in range(1, m) if cnt[g] == 0)
        tabu_add = [0] * m
        tabu_rem = [0] * m
        best_U = U
        last_improve = 0
        step = 0
        while U > 0:
            step += 1
            if (step & 31) == 0 and time.monotonic() > deadline:
                return None
            if step - last_improve > 4000:
                break  # stagnation: restart from a fresh random set
            unc = [g for g in range(1, m) if cnt[g] == 0]
            g = unc[rng.randrange(len(unc))]
            cset = set()
            for s in S:
                for v in ((s + g) % m, (s - g) % m):
                    if v not in inS:
                        cset.add(v)
            cands = list(cset)
            if not cands:
                continue
            if len(cands) > 12:
                cands = rng.sample(cands, 12)
            bestv = None
            bestval = None
            ties = 0
            for y in cands:
                for i in range(k):
                    x = S[i]
                    others = S[:i] + S[i + 1:]
                    c1 = _bump(cnt, others, x, m, -1)
                    c2 = _bump(cnt, others, y, m, 1)
                    val = U + c1 + c2
                    _bump(cnt, others, y, m, -1)
                    _bump(cnt, others, x, m, 1)
                    if (tabu_add[y] > step or tabu_rem[x] > step) and val >= best_U:
                        continue
                    if bestval is None or val < bestval:
                        bestval = val
                        bestv = (i, x, y)
                        ties = 1
                    elif val == bestval:
                        ties += 1
                        if rng.randrange(ties) == 0:
                            bestv = (i, x, y)
            if bestv is None:
                continue
            i, x, y = bestv
            others = S[:i] + S[i + 1:]
            _bump(cnt, others, x, m, -1)
            _bump(cnt, others, y, m, 1)
            S[i] = y
            inS.discard(x)
            inS.add(y)
            U = bestval
            tabu_add[x] = step + tenure_base + rng.randrange(5)
            tabu_rem[y] = step + tenure_base + rng.randrange(5)
            if U < best_U:
                best_U = U
                last_improve = step
        if U == 0:
            return sorted(S)
    return None


def _haar_search(k, rng, deadline):
    """Climb m upward from 0.8 * (k^2-k+1), keeping the largest m with a difference cover. Returns (m, S) or None."""
    if k < 2:
        return None
    mmax = k * (k - 1) + 1
    m = max(k, int(0.80 * mmax))
    best = None
    fails = 0
    while m <= mmax:
        now = time.monotonic()
        if now >= deadline:
            break
        remaining = deadline - now
        slice_ = remaining / 3.0 if fails == 0 else remaining / 2.0
        S = _cover_walk(k, m, rng, min(deadline, now + max(0.5, slice_)))
        if S is not None:
            best = (m, S)
            m += 1
            fails = 0
        else:
            fails += 1
            if fails >= 2:
                break
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4)
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * float(time_limit), 50.0)
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 17 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D == 3:
        # Arc-extended projective planes first: cheap, and a strong fallback (order 394 at d = 16).
        cands = _arc_candidates(d, start + 0.2 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands[:2]:
            consider(n_c, E_c)
        # Then the difference-cover Haar search with the remaining time.
        if d >= 2:
            res = _haar_search(d, rng, deadline)
            if res is not None:
                m, S = res
                n, E = lib.haar_graph(m, S)
                consider(n, E)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
