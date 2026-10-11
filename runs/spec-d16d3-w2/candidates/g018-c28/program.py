import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generic helpers
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
    """Incidence graph of PG(2,q) plus, per element of S, an A-vertex and a B-vertex.
    Returns (n, edges, side)."""
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
    """For each prime power q with q + 1 <= d, build the arc-extended PG(2,q) graph."""
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
# New construction: Haar graphs from difference covers.
#
# H(m, S) has parts a_i, b_i (i in Z_m) with a_i ~ b_{i+s} for s in S.
# It is k-regular with k = |S| and bipartite. Its diameter is at most 3
# iff S - S covers all of Z_m (a_i to a_j and b_i to b_j need a difference
# in S - S; a_i to b_j then follows from D + S = Z_m, where D = S - S).
# Maximising m for fixed k = d is therefore a difference-cover problem with
# m <= k^2 - k + 1 (the Moore bound). We anneal over S directly.
# ----------------------------------------------------------------------------

def _swap(S, cnt, inS, m, i, nw):
    """Replace S[i] by nw, updating ordered-difference counts cnt.
    Returns the change in the number of uncovered nonzero residues."""
    old = S[i]
    delta = 0
    k = len(S)
    for j in range(k):
        if j == i:
            continue
        b = S[j]
        for x in ((old - b) % m, (b - old) % m):
            cnt[x] -= 1
            if cnt[x] == 0:
                delta += 1
    S[i] = nw
    inS[old] = False
    inS[nw] = True
    for j in range(k):
        if j == i:
            continue
        b = S[j]
        for x in ((nw - b) % m, (b - nw) % m):
            if cnt[x] == 0:
                delta -= 1
            cnt[x] += 1
    return delta


def _diff_cover(m, k, rng, budget_end):
    """Simulated annealing for a k-subset S of Z_m (containing 0) with S - S = Z_m.
    Returns S as a list, or None if the budget runs out."""
    if k > m:
        return None
    S = [0] + rng.sample(range(1, m), k - 1)
    inS = [False] * m
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)
    if unc == 0:
        return list(S)
    if m == k:
        return None  # no non-member to move to, and not covered
    start = time.monotonic()
    span = max(1e-3, budget_end - start)
    T = 1.0
    it = 0
    while True:
        it += 1
        if it & 255 == 0:
            now = time.monotonic()
            if now >= budget_end:
                return None
            frac = min(1.0, (now - start) / span)
            T = 1.0 * (0.03 ** frac)
        i = rng.randrange(1, k)
        nw = rng.randrange(1, m)
        if inS[nw]:
            continue
        old = S[i]
        delta = _swap(S, cnt, inS, m, i, nw)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            unc += delta
            if unc == 0:
                return list(S)
        else:
            _swap(S, cnt, inS, m, i, old)


def _haar_search(k, deadline, rng):
    """Find the largest m (ascending) for which a difference cover of size k exists in Z_m.
    Returns (n, edges) of the best valid Haar graph found, or None."""
    best = None
    mmax = k * k - k + 1
    m = max(k, 2)
    fails = 0
    while m <= mmax and time.monotonic() < deadline and fails < 3:
        remaining = deadline - time.monotonic()
        budget = min(max(0.5, remaining * 0.2), 8.0)
        S = _diff_cover(m, k, rng, time.monotonic() + budget)
        if S is not None:
            n, E = lib.haar_graph(m, S)
            if lib.is_valid(n, E, k, 3):
                best = (n, E)
            fails = 0
        else:
            fails += 1
        m += 1
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D >= 4).
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
    deadline = start + 0.7 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is d-regular.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, E

    # Arc-extended projective plane candidates (fast, a strong baseline for D = 3).
    if D >= 3:
        arc_deadline = start + 0.2 * time_limit
        for n_c, E_c, _side in _arc_candidates(d, arc_deadline,
                                               random.Random(seed * 7919 + d)):
            consider(n_c, E_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main bold search: Haar graphs over difference covers of Z_m with |S| = d.
    # Valid for diameter 3, hence for any D >= 3.
    if D >= 3 and d >= 2 and time.monotonic() < deadline:
        hs = _haar_search(d, deadline, random.Random(seed * 104729 + d))
        if hs is not None:
            consider(hs[0], hs[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
