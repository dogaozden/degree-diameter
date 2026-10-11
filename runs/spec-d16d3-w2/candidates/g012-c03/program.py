import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc helpers (D = 3 arc-extended incidence graphs)
# ----------------------------------------------------------------------------

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
# NEW for this island: focused walk for difference covers.
#
# A Haar graph H(m, S) with |S| = k has diameter 3 exactly when S - S = Z_m
# (a difference cover). Instead of annealing over random swaps, we walk
# with a focus on UNCOVERED differences (WalkSAT style): pick an uncovered
# g, then move some element of S to y = s + g for an anchor s in S, which
# covers g directly. Random noise moves keep the walk from cycling. Every
# swap updates the ordered-difference counts in O(k).
# ----------------------------------------------------------------------------

def _swap(S, i, y, cnt, m):
    """Replace S[i] by y (y not in S), update difference counts, return the change in #uncovered."""
    x = S[i]
    d = 0
    for j, s in enumerate(S):
        if j == i:
            continue
        g = (x - s) % m
        cnt[g] -= 1
        if cnt[g] == 0:
            d += 1
        g = (s - x) % m
        cnt[g] -= 1
        if cnt[g] == 0:
            d += 1
    for j, s in enumerate(S):
        if j == i:
            continue
        g = (y - s) % m
        if cnt[g] == 0:
            d -= 1
        cnt[g] += 1
        g = (s - y) % m
        if cnt[g] == 0:
            d -= 1
        cnt[g] += 1
    S[i] = y
    return d


def _cover_walk(k, m, rng, deadline):
    """Find S subset of Z_m with |S| = k and S - S = Z_m. Returns sorted S, or None on timeout."""
    if m < k or k < 2:
        return None
    if m == k:
        return list(range(m))
    S = rng.sample(range(m), k)
    in_s = set(S)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    U = sum(1 for g in range(1, m) if cnt[g] == 0)
    T = 0.35
    it = 0
    while U > 0:
        it += 1
        if (it & 511) == 0 and time.monotonic() > deadline:
            return None
        if rng.random() < 0.75:
            # Focused move: cover a random uncovered difference g.
            g = None
            for _ in range(50):
                c = rng.randrange(1, m)
                if cnt[c] == 0:
                    g = c
                    break
            if g is None:
                g = rng.choice([c for c in range(1, m) if cnt[c] == 0])
            j = rng.randrange(k)           # anchor index, stays in S
            y = (S[j] + g) % m
            if y in in_s:
                continue
            i = rng.randrange(k - 1)       # replaced index, must differ from anchor
            if i >= j:
                i += 1
        else:
            # Noise move: random replacement.
            i = rng.randrange(k)
            y = rng.randrange(m)
            if y in in_s:
                continue
        x = S[i]
        delta = _swap(S, i, y, cnt, m)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            in_s.discard(x)
            in_s.add(y)
            U += delta
        else:
            _swap(S, i, x, cnt, m)
    return sorted(S)


def _haar_walk_search(k, rng, deadline):
    """Find the largest m with a difference cover of size k; returns (m, S) or None.

    Starts near 0.82 * the Moore-type cap k(k-1)+1 and climbs upward while covers are found.
    """
    if k < 2:
        return None
    mmax = k * (k - 1) + 1
    m = min(mmax, int(0.82 * mmax) + 1)
    best = None
    tries = 0
    while best is None and m >= k and tries < 3:
        now = time.monotonic()
        if now >= deadline:
            break
        slice_ = max(1.0, (deadline - now) / 2.0)
        S = _cover_walk(k, m, rng, min(deadline, now + slice_))
        tries += 1
        if S is not None:
            best = (m, S)
        else:
            m -= 1
    if best is None:
        return None
    m = best[0] + 1
    while m <= mmax and time.monotonic() < deadline:
        now = time.monotonic()
        slice_ = max(1.0, (deadline - now) / 2.0)
        S = _cover_walk(k, m, rng, min(deadline, now + slice_))
        if S is None:
            break
        best = (m, S)
        m += 1
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
    budget = min(0.8 * float(time_limit), 48.0)
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
        # Arc-extended projective plane (order 2m + 2k).
        cands = _arc_candidates(d, start + 0.2 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands[:1]:
            consider(n_c, E_c)
        # Haar graph from a difference cover found by the focused walk (order 2m).
        if d >= 2:
            res = _haar_walk_search(d, rng, start + 0.9 * budget)
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
