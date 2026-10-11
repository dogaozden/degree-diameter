"""Arc-base plus growth-and-repair search for bipartite graphs of diameter D (target: d=16, D=3).

Construction:
1. Base: the point-line incidence graph of PG(2, q), extended by one new X-vertex per
   point of an arc S and one new Y-vertex per line of S. The arc condition keeps every
   old vertex within degree d. This reproduces the 394-vertex record for d=16, D=3.
2. Growth: repeatedly add one new X-vertex and one new Y-vertex, greedily attach them to
   spare opposite-side vertices, then anneal with degree-preserving, bipartite-preserving
   2-switches that minimise the number of vertex pairs at distance > D. A change is kept
   only if the result passes lib.is_valid.
3. Fallback: K_{d,d} (diameter 2), or the verified base, is returned if nothing better
   validates.

Degree-preserving 2-switches never raise a vertex's degree, and greedy edge insertion
between spare X and Y vertices never increases a distance, so the search only moves
between valid-degree graphs. Whether this beats the 394 record is not guaranteed.
"""
import math
import random
import time

import lib


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


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
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, pg_edges, point_lines, line_points, S):
    """Old incidence plus a new X-vertex per point of S and a new Y-vertex per line of S.

    X side: points 0..m-1 and new X-vertices 2m..2m+k-1.
    Y side: lines m..2m-1 and new Y-vertices 2m+k..2m+2k-1.
    """
    k = len(S)
    n = 2 * m + 2 * k
    E = list(pg_edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        y = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, y))
    return n, E


def _arc_base(d, deadline, rng):
    """Best arc-extended PG(2,q) graph over prime powers q with q + 1 <= d. Returns (n, edges, m, k) or None."""
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, pg_edges, point_lines, line_points, index = _pg_data(q)
        if s == 0:
            S = []
        else:
            S = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
            if s >= 2:
                cs = _conic_set(q, index, lib.GF(q))
                if len(cs) > len(S) and _loads_ok(cs, s, m, point_lines, line_points):
                    S = cs
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, E = _arc_graph(m, pg_edges, point_lines, line_points, S)
        if best is None or n_c > best[0]:
            best = (n_c, E, m, len(S))
    return best


def _to_state(n, edges, side):
    """Adjacency sets and oriented edge list (X endpoint first). Returns (None, None) if not bipartite."""
    adj = [set() for _ in range(n)]
    E = []
    for u, v in edges:
        if side[u] == side[v]:
            return None, None
        x, y = (u, v) if side[u] == 0 else (v, u)
        adj[x].add(y)
        adj[y].add(x)
        E.append((x, y))
    return adj, E


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable counts as bad)."""
    nbr = [list(a) for a in adj]
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _fill(n, side, adj, E, d, rng):
    """Greedily add X-Y edges between spare-degree vertices. Never increases any distance."""
    X = [v for v in range(n) if side[v] == 0 and len(adj[v]) < d]
    Y = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
    pairs = [(x, y) for x in X for y in Y if y not in adj[x]]
    rng.shuffle(pairs)
    for x, y in pairs:
        if len(adj[x]) < d and len(adj[y]) < d and y not in adj[x]:
            adj[x].add(y)
            adj[y].add(x)
            E.append((x, y))


def _repair(n, adj, E, D, rng, deadline, steps):
    """Anneal with degree- and bipartiteness-preserving 2-switches to minimise bad pairs."""
    cost = _bad_pairs(n, adj, D)
    T = 0.6
    for _ in range(steps):
        if cost == 0 or time.monotonic() > deadline or len(E) < 2:
            break
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a, b = E[i]   # a in X, b in Y
        c, e = E[j]   # c in X, e in Y
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        # Replace (a,b),(c,e) by (a,e),(c,b): all degrees unchanged.
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _bad_pairs(n, adj, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            E[i] = (a, e)
            E[j] = (c, b)
            cost = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
        T = max(0.05, T * 0.995)
    return cost


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    # Base: arc-extended projective plane incidence graph (diameter 3, valid for D >= 3).
    base = _arc_base(d, start + 0.2 * (deadline - start), rng)
    if base is None:
        return best
    n, edges, m, k = base
    if n > best[0] and lib.is_valid(n, edges, d, D):
        best = (n, edges)

    # Growth-and-repair: add one X and one Y vertex, then anneal toward zero bad pairs.
    bound = lib.moore_bound(d, D)
    side = [1 if (m <= v < 2 * m or v >= 2 * m + k) else 0 for v in range(n)]
    adj, E = _to_state(n, edges, side)
    if adj is None:
        return best

    while time.monotonic() < deadline and n + 2 <= bound:
        snap_adj = [set(a) for a in adj]
        snap_E = list(E)
        snap_side = list(side)
        snap_n = n

        side.extend([0, 1])
        adj.extend([set(), set()])
        n += 2
        _fill(n, side, adj, E, d, rng)
        cost = _repair(n, adj, E, D, rng, deadline, steps=400)

        if cost == 0 and lib.is_valid(n, E, d, D):
            best = (n, list(E))
        else:
            adj, E, side, n = snap_adj, snap_E, snap_side, snap_n

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
