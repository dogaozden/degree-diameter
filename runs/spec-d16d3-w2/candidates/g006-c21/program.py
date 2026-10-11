import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline: arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence. Each old vertex has degree q+1, so spare
# capacity s = d - q - 1. Choose S (an arc-like set) with every line holding
# at most s points of S and every point lying on at most s lines indexed by S.
# Add a new X-vertex per P in S (joined to the lines through P) and a new
# Y-vertex per j in S (joined to the points on j). Then saturate with spare
# X-Y edges. Diameter stays 3 for any such S.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    pts = lib.projective_points(q)
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new X-vertex per P in S and a new Y-vertex per j in S."""
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


def _saturate(n, edges, m, k, d, rng):
    """Add every missing X-Y edge while both endpoints have spare degree."""
    E = set()
    for u, v in edges:
        E.add((u, v) if u < v else (v, u))
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    X = [v for v in range(n) if v < m or 2 * m <= v < 2 * m + k]
    Y = [v for v in range(n) if m <= v < 2 * m or v >= 2 * m + k]
    spare_x = [v for v in X if deg[v] < d]
    spare_y = [v for v in Y if deg[v] < d]
    pairs = [(x, y) for x in spare_x for y in spare_y]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d:
            continue
        key = (x, y) if x < y else (y, x)
        if key in E:
            continue
        E.add(key)
        deg[x] += 1
        deg[y] += 1
    return n, sorted(E)


def _arc_baseline(d, deadline, rng):
    """Best arc-extended PG(2,q) graph over prime powers q with q + 1 < d, or None."""
    best = None
    for q in range(min(d - 1, 23), 1, -1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp, index = _pg_data(q)
        cands = [_greedy_arc(m, s, pl, lp, rng, 40, deadline)]
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not S or not _loads_ok(S, s, m, pl, lp):
            continue
        n_c, e_c = _arc_graph(m, edges, pl, lp, S)
        n_c, e_c = _saturate(n_c, e_c, m, len(S), d, rng)
        if best is None or n_c > best[0]:
            best = (n_c, e_c)
    return best


# ----------------------------------------------------------------------------
# Bold change: grow-and-anneal search on the bipartite graph itself.
#
# State: a bipartite graph with degree cap d. Moves preserve the cap:
#   swap  : double edge swap (x1y1, x2y2) -> (x1y2, x2y1), keeps degrees
#   steal : attach x to a full y by taking y's edge to some x2
#   fill  : add any X-Y edge between two deficit vertices (never hurts)
# Cost = number of vertex pairs at distance > D. When cost hits zero the
# graph is valid, so we record it and grow by one X-vertex and one Y-vertex.
# ----------------------------------------------------------------------------

def _cost(adj, n, D):
    """Number of unordered pairs at distance > D (unreachable counts)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _color(n, adj):
    """Bipartition: True for colour-0 vertices (the X side)."""
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
    return [c == 0 for c in color]


def _to_edges(adj, n, isX):
    return [(u, v) for u in range(n) if isX[u] for v in adj[u]]


def _fill(adj, X, Y, d, rng):
    """Add X-Y edges between deficit vertices while possible."""
    xs = [x for x in X if len(adj[x]) < d]
    ys = [y for y in Y if len(adj[y]) < d]
    rng.shuffle(xs)
    rng.shuffle(ys)
    for x in xs:
        for y in ys:
            if len(adj[x]) >= d:
                break
            if len(adj[y]) < d and y not in adj[x]:
                adj[x].add(y)
                adj[y].add(x)


def _grow_search(d, D, best, moore, deadline, rng):
    n, edges = best
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    isX = _color(n, adj)
    X = [v for v in range(n) if isX[v]]
    Y = [v for v in range(n) if not isX[v]]
    _fill(adj, X, Y, d, rng)
    best_n, best_e = best
    cost = _cost(adj, n, D)
    T = 1.0
    it = 0
    while time.monotonic() < deadline:
        if cost == 0:
            if n > best_n:
                e = _to_edges(adj, n, isX)
                if lib.is_valid(n, e, d, D):
                    best_n, best_e = n, e
            if n + 2 > moore:
                break
            n += 2
            adj.append(set())
            adj.append(set())
            isX.append(True)
            isX.append(False)
            X.append(n - 2)
            Y.append(n - 1)
            _fill(adj, X, Y, d, rng)
            cost = _cost(adj, n, D)
            T = 1.0
            continue

        it += 1
        T = max(0.25, T * 0.9995)
        if it % 100 == 0:
            _fill(adj, X, Y, d, rng)
            cost = _cost(adj, n, D)
            continue

        r = rng.random()
        if r < 0.6:
            x1 = rng.choice(X)
            if not adj[x1]:
                continue
            y1 = rng.choice(tuple(adj[x1]))
            x2 = rng.choice(X)
            if x2 == x1 or not adj[x2]:
                continue
            y2 = rng.choice(tuple(adj[x2]))
            if y2 in adj[x1] or y1 in adj[x2]:
                continue
            adj[x1].discard(y1); adj[y1].discard(x1)
            adj[x2].discard(y2); adj[y2].discard(x2)
            adj[x1].add(y2); adj[y2].add(x1)
            adj[x2].add(y1); adj[y1].add(x2)
            c2 = _cost(adj, n, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                adj[x1].discard(y2); adj[y2].discard(x1)
                adj[x2].discard(y1); adj[y1].discard(x2)
                adj[x1].add(y1); adj[y1].add(x1)
                adj[x2].add(y2); adj[y2].add(x2)
        else:
            x = rng.choice(X)
            if len(adj[x]) >= d:
                continue
            y = rng.choice(Y)
            if y in adj[x]:
                continue
            if len(adj[y]) < d:
                adj[x].add(y); adj[y].add(x)
                cost = _cost(adj, n, D)
                continue
            x2 = rng.choice(tuple(adj[y]))
            adj[x2].discard(y); adj[y].discard(x2)
            adj[x].add(y); adj[y].add(x)
            c2 = _cost(adj, n, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                adj[x].discard(y); adj[y].discard(x)
                adj[x2].add(y); adj[y].add(x2)
    return best_n, best_e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = (n0, e0)

    if D >= 3:
        arc = _arc_baseline(d, start + 0.25 * budget, rng)
        if arc is not None and arc[0] > best[0] and lib.is_valid(arc[0], arc[1], d, D):
            best = arc

    moore = lib.moore_bound(d, D)
    if best[0] < moore and time.monotonic() < deadline:
        try:
            cand = _grow_search(d, D, best, moore, deadline, rng)
        except Exception:
            cand = None
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    if not lib.is_valid(best[0], best[1], d, D):
        best = (n0, e0)
    return best
