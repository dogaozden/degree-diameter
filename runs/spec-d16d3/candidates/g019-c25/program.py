import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base and arc extensions (diameter 3).
# ----------------------------------------------------------------------------

def _best_q(d):
    """Largest prime power q with q + 1 <= d (capped for speed)."""
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


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


def _loads_ok(S, s, m, point_lines, line_points):
    """Every line holds <= s points of S, and every point lies on <= s lines indexed by S."""
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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG incidence plus one new A-vertex per point of S and one new B-vertex per line of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """One arc-extended candidate (n, edges) per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)]
        if s >= 2:
            cands.append(_conic_set(q, index, lib.GF(q)))
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Spare-recycling hill-climb: add new vertices whose neighbourhoods are found
# by local search over the spare capacity of the current graph.
#
# A new vertex v on side 1-c with neighbourhood N (subset of side c with spare
# degree) keeps the diameter iff every vertex is within distance D-1 of N in the
# old graph. We start from a greedy set cover of the radius-(D-1) balls and then
# hill-climb on the exact number of ordered pairs left at distance > D.
# ----------------------------------------------------------------------------

def _adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _ball_r(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _cost_with(n, adj, N, D):
    """Ordered pairs at distance > D after adding a new vertex n adjacent to N."""
    Ns = set(N)
    full = [adj[v] + [n] if v in Ns else adj[v] for v in range(n)]
    full.append(list(N))
    m = n + 1
    ball = [1 << v for v in range(m)]
    for _ in range(D):
        new = []
        for v in range(m):
            x = ball[v]
            for u in full[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(m - b.bit_count() for b in ball)


def _start_nbhd(cands, ball, full, k, rng):
    """Greedy cover of `full` by the balls of cands, padded with random candidates to size k."""
    pool = list(cands)
    covered = 0
    chosen = []
    while len(chosen) < k and covered != full and pool:
        best = max(pool, key=lambda s: (ball[s] & ~covered).bit_count())
        if (ball[best] & ~covered) == 0:
            break
        chosen.append(best)
        pool.remove(best)
        covered |= ball[best]
    rest = [s for s in cands if s not in chosen]
    rng.shuffle(rest)
    while len(chosen) < k and rest:
        chosen.append(rest.pop())
    return chosen


def _search_nbhd(n, adj, cands, N, D, deadline, rng, iters=150):
    """Hill-climb a neighbourhood N (drawn from cands) that makes the new vertex valid."""
    N = list(N)
    cost = _cost_with(n, adj, N, D)
    for _ in range(iters):
        if cost == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(len(N))
        x = rng.choice(cands)
        if x in N:
            continue
        T = N[:]
        T[i] = x
        ct = _cost_with(n, adj, T, D)
        if ct <= cost or rng.random() < 0.03:
            N, cost = T, ct
    return cost == 0, N


def _grow_hill(n, edges, d, D, deadline, rng):
    """Repeatedly add a valid new vertex while spare capacity and time allow."""
    edges = list(edges)
    while time.monotonic() < deadline:
        adj = _adj(n, edges)
        color = _bipartition(n, adj)
        deg = [len(a) for a in adj]
        ball = _ball_r(n, adj, D - 1)
        full = (1 << n) - 1
        grown = False
        for c in rng.sample((0, 1), 2):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            k = min(d, len(cands))
            N0 = _start_nbhd(cands, ball, full, k, rng)
            ok, N = _search_nbhd(n, adj, cands, N0, D, deadline, rng)
            if ok:
                edges.extend((s, n) for s in N)
                n += 1
                grown = True
                break
            if time.monotonic() >= deadline:
                break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D < 3:
        return best

    q = _best_q(d)
    if q is None:
        return best

    cands = [lib.projective_plane_incidence(q)]
    cands += _arc_extensions(d, start + 0.3 * time_limit, rng)
    cands = [c for c in cands if c[0] > 0]
    cands.sort(key=lambda c: -c[0])

    base_n, base_e = cands[0]
    if not lib.is_valid(base_n, base_e, d, D):
        return best

    n2, e2 = _grow_hill(base_n, base_e, d, D, end, rng)
    for n_c, e_c in ((n2, e2), (base_n, base_e)):
        if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)
            break
    return best
