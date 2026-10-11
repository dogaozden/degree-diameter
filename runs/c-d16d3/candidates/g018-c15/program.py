import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy for D >= 3.
#
# 1. Baseline: arc-extended projective plane graphs (diameter 3). For d = 16
#    this reproduces the record 394 (PG(2,13) plus conics on both sides).
#
# 2. New construction: cyclic Haar graphs H(Z_m, S) with |S| = d. Vertices are
#    a_i and b_j (i, j in Z_m), with a_i ~ b_j iff j - i is in S. This graph is
#    bipartite and d-regular on 2m vertices. Its diameter is at most 3 whenever
#    S - S = Z_m: same-side pairs are at distance 2 through differences, and
#    cross pairs at distance 3 through S - S + S. So the search is a difference
#    covering problem. Larger m beats the record, and the Moore-type ceiling is
#    m <= d(d-1)+1. We run simulated annealing on S (with 0 fixed in S) to
#    minimize the number of uncovered nonzero residues, and increase m while
#    solutions are found in time.
#
# Every candidate is checked with lib.is_valid before it is kept. The fallback
# is always a valid graph (K_{d,d}, or the best baseline found).
# ----------------------------------------------------------------------------


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Difference-covering search for cyclic Haar graphs.
# ----------------------------------------------------------------------------

def _swap(cnt, others, a, b, m):
    """Replace element a by b in a set whose other elements are `others`.

    Updates the ordered-difference counts cnt in place and returns the change in
    the number of uncovered nonzero residues. Calling _swap(cnt, others, b, a, m)
    undoes it exactly.
    """
    d = 0
    for t in others:
        x = (a - t) % m
        cnt[x] -= 1
        if cnt[x] == 0:
            d += 1
        x = (t - a) % m
        cnt[x] -= 1
        if cnt[x] == 0:
            d += 1
    for t in others:
        x = (b - t) % m
        if cnt[x] == 0:
            d -= 1
        cnt[x] += 1
        x = (t - b) % m
        if cnt[x] == 0:
            d -= 1
        cnt[x] += 1
    return d


def _cover_search(m, k, rng, deadline):
    """Find S in Z_m with |S| = k, 0 in S, and S - S = Z_m. Return sorted S or None."""
    if k < 2 or k > m:
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
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T = 0.5
    it = 0
    while unc > 0:
        it += 1
        if it % 256 == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            frac = (now - start) / span
            T = 0.6 * (1.0 - frac) + 0.03
        i = rng.randrange(1, k)
        y = rng.randrange(1, m)
        if inS[y]:
            continue
        old = S[i]
        others = S[:i] + S[i + 1:]
        dlt = _swap(cnt, others, old, y, m)
        if dlt <= 0 or rng.random() < math.exp(-dlt / T):
            S[i] = y
            inS[old] = False
            inS[y] = True
            unc += dlt
        else:
            _swap(cnt, others, y, old, m)  # exact revert
    return sorted(S)


def _haar_search(d, m_lo, deadline, rng):
    """Increase m from m_lo while a difference covering of size d is found in time.

    Returns (m, S) for the largest m found, or None.
    """
    best = None
    bound = d * (d - 1) + 1  # counting bound for S - S = Z_m
    m = m_lo
    while m <= bound and time.monotonic() < deadline:
        now = time.monotonic()
        slice_end = now + max(1.0, (deadline - now) * 0.5)
        S = _cover_search(m, d, rng, min(deadline, slice_end))
        if S is None:
            break
        best = (m, S)
        m += 1
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3 and d >= 2:
        # Baseline: arc-extended projective plane graphs (diameter 3).
        arc_rng = random.Random(seed * 7919 + d)
        arc_deadline = start + 0.25 * time_limit
        for n_c, e_c in sorted(_arc_extensions(d, arc_deadline, arc_rng), key=lambda t: -t[0]):
            consider(n_c, e_c)

        # Diameter 4 baseline when allowed.
        if D >= 4 and time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        # New construction: cyclic Haar graphs from difference coverings.
        # Valid for every D >= 3 since their diameter is 3.
        if time.monotonic() < deadline:
            m_lo = best_n // 2 + 1
            found = _haar_search(d, m_lo, deadline, random.Random(seed * 104729 + d))
            if found is not None:
                m, S = found
                hn, he = lib.haar_graph(m, S)
                consider(hn, he)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
