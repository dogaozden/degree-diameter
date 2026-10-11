import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Moore bound
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


# ----------------------------------------------------------------------------
# NEW for D = 3: Haar graphs over NON-CYCLIC abelian groups.
#
# For an abelian group G of order N and a k-subset S of G, the bipartite graph
# with parts A = G and B = G and edges a_g ~ b_{g+s} (s in S) is k-regular and
# has order 2N. Two A-vertices (or two B-vertices) are at distance <= 2 iff
# every nonzero element of G is a difference s - t. Mixed pairs are at distance
# <= 3 because S - S + S covers G. So diameter 3 holds iff S - S = G \ {0}.
#
# The parent only searched cyclic groups Z_m. Here every group Z_a x Z_b with
# a*b = N is tried for each order N, and the order is climbed upward. Groups
# with several small factors often admit difference covers at orders where the
# cyclic group has none, so this can reach larger N than the cyclic search.
# ----------------------------------------------------------------------------

def _group_pairs(N):
    """Return (a, b) with a*b = N, a <= b, cyclic (1, N) first."""
    out = [(1, N)]
    for a in range(2, math.isqrt(N) + 1):
        if N % a == 0:
            out.append((a, N // a))
    return out


_TABLE_CACHE = {}


def _sub_table(a, b):
    """sub[i][j] = i - j in Z_a x Z_b, elements coded as x*b + y."""
    key = (a, b)
    if key in _TABLE_CACHE:
        return _TABLE_CACHE[key]
    N = a * b
    coords = [divmod(i, b) for i in range(N)]
    sub = [[0] * N for _ in range(N)]
    for i, (x1, y1) in enumerate(coords):
        row = sub[i]
        for j, (x2, y2) in enumerate(coords):
            row[j] = ((x1 - x2) % a) * b + (y1 - y2) % b
    _TABLE_CACHE[key] = sub
    return sub


def _anneal_cover(N, k, sub, rng, deadline):
    """Find S, |S| = k, in the group with sub-table `sub`, whose differences cover all nonzero elements."""
    S = rng.sample(range(N), k)
    inS = set(S)
    cnt = [0] * N
    for a in S:
        for b in S:
            if a != b:
                cnt[sub[a][b]] += 1
    unc = sum(1 for g in range(1, N) if cnt[g] == 0)
    T = 1.0
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        if it % 100000 == 0:
            T = 0.6
        T = max(0.05, T * 0.99995)
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(N)
        if y in inS:
            continue
        others = S[:i] + S[i + 1:]
        delta = 0
        # Remove x's differences.
        for s in others:
            g = sub[x][s]
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
            g = sub[s][x]
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
        # Add y's differences.
        for s in others:
            g = sub[y][s]
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
            g = sub[s][y]
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            inS.discard(x)
            inS.add(y)
            unc += delta
        else:
            for s in others:
                cnt[sub[y][s]] -= 1
                cnt[sub[s][y]] -= 1
            for s in others:
                cnt[sub[x][s]] += 1
                cnt[sub[s][x]] += 1
    return sorted(S)


def _haar_search(k, rng, deadline):
    """Climb the group order N upward; for each N try all abelian groups of order N.

    Returns (N, a, b, S) for the largest N found, or None.
    """
    if k < 2:
        return None
    mmax = k * (k - 1) + 1
    best = None
    fails = 0
    N = k
    while N <= mmax and time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        slice_end = min(deadline, time.monotonic() + max(0.3, remaining / 4.0))
        found = None
        for a, b in _group_pairs(N):
            if time.monotonic() >= slice_end:
                break
            sub = _sub_table(a, b)
            S = _anneal_cover(N, k, sub, rng, slice_end)
            if S is not None:
                found = (N, a, b, S)
                break
        if found is not None:
            best = found
            fails = 0
        else:
            fails += 1
            if fails >= 3:
                break
        N += 1
    return best


def _haar_edges(N, a, b, S):
    """Edges of the Haar-type graph over Z_a x Z_b: A-vertex g joins B-vertex N + (g + s)."""
    coords = [divmod(i, b) for i in range(N)]

    def add(g, s):
        x1, y1 = coords[g]
        x2, y2 = coords[s]
        return ((x1 + x2) % a) * b + (y1 + y2) % b

    E = []
    for s in S:
        for g in range(N):
            E.append((g, N + add(g, s)))
    return 2 * N, E


# ----------------------------------------------------------------------------
# Parent D = 3 secondary: arc-extended projective plane.
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
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
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
    budget = min(0.8 * float(time_limit), 46.0)
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

    if D == 3 and d >= 2:
        # Primary: Haar-type graph over an abelian group of order N with a difference cover of size d.
        res = _haar_search(d, rng, start + 0.7 * budget)
        if res is not None:
            N, a, b, S = res
            n, E = _haar_edges(N, a, b, S)
            consider(n, E)
        # Secondary: arc-extended projective plane.
        cands = _arc_candidates(d, start + 0.9 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c in cands[:1]:
            consider(n_c, E_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
