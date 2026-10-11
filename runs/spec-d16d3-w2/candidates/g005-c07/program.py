import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc helpers (D = 3). The arc-extended incidence graph
# PG(2,q) + {A_t, B_t : t in S} gives 2(q^2+q+1) + 2|S| vertices.
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
    return n, E


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
# Haar graphs from difference covers (D = 3).
#
# H(m, S) has parts Z_m and Z_m with a_i ~ b_{i+s}, s in S. It has diameter 3
# exactly when S - S = Z_m (a difference cover), and has order 2m. To beat the
# arc record of 394 for d = 16 we need m >= 198 with |S| = 16.
#
# The cover search is a tabu search. Each step picks an uncovered difference g
# and tries moves that create g (replace some s_i by s_j + g or s_j - g). It
# takes the best non-tabu move, and perturbs S after a long stall.
# ----------------------------------------------------------------------------

def _move(S, cnt, i, y, m):
    """Replace S[i] by y, updating the ordered-difference counts cnt. Returns the change in uncovered count."""
    x = S[i]
    delta = 0
    for j, s in enumerate(S):
        if j == i:
            continue
        for g in ((x - s) % m, (s - x) % m):
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
    for j, s in enumerate(S):
        if j == i:
            continue
        for g in ((y - s) % m, (s - y) % m):
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
    S[i] = y
    return delta


def _cover_search(k, m, rng, deadline):
    """Find S subset of Z_m with |S| = k and S - S = Z_m by tabu search. Returns sorted S, or None."""
    S = rng.sample(range(m), k)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    tabu = [0] * m
    step = 0
    best = unc
    stall = 0
    while unc > 0:
        step += 1
        if (step & 31) == 0 and time.monotonic() > deadline:
            return None
        if stall > 4000:
            # Perturb: random replacements to escape the basin.
            for _ in range(3):
                i = rng.randrange(k)
                y = rng.randrange(m)
                if y not in S:
                    unc += _move(S, cnt, i, y, m)
            stall = 0
            best = unc
            continue
        uncs = [g for g in range(1, m) if cnt[g] == 0]
        g = rng.choice(uncs)
        cands = []
        for j in range(k):
            for y in ((S[j] + g) % m, (S[j] - g) % m):
                if y in S:
                    continue
                for i in range(k):
                    if i != j:
                        cands.append((i, y))
        if len(cands) > 48:
            cands = rng.sample(cands, 48)
        bestd = None
        bestc = []
        for i, y in cands:
            if tabu[y] > step:
                continue
            x = S[i]
            dl = _move(S, cnt, i, y, m)
            _move(S, cnt, i, x, m)
            if bestd is None or dl < bestd:
                bestd = dl
                bestc = [(i, y)]
            elif dl == bestd:
                bestc.append((i, y))
        if not bestc:
            stall += 1
            continue
        i, y = rng.choice(bestc)
        x = S[i]
        unc += _move(S, cnt, i, y, m)
        tabu[x] = step + rng.randint(4, 10)
        if unc < best:
            best = unc
            stall = 0
        else:
            stall += 1
    return sorted(S)


def _haar_search(k, m0, mmax, rng, deadline):
    """Try m = m0, m0+1, ... while covers are found. Returns (m, S) for the largest m found, or None."""
    best = None
    m = m0
    while m <= mmax and time.monotonic() < deadline:
        now = time.monotonic()
        slice_end = now + 0.75 * (deadline - now)
        S = _cover_search(k, m, rng, min(deadline, slice_end))
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
    budget = min(0.85 * float(time_limit), 48.0)
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
        # Baseline: arc-extended projective plane (fast, gives the record for d = 16).
        cands = _arc_candidates(d, start + 0.3 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c in cands[:1]:
            consider(n_c, E_c)

        # Improvement: a Haar graph H(m, S) with |S| = d and S - S = Z_m has order 2m.
        # Only m with 2m > current best can help, so search upward from there with the
        # remaining time.
        if d >= 3:
            m0 = best_n // 2 + 1
            mmax = d * (d - 1) + 1
            if m0 <= mmax:
                res = _haar_search(d, m0, mmax, rng, deadline)
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
