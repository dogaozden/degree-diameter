import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy
#
# 1. Build a valid base graph:
#    - D = 1 or d = 1: K2.  d = 2: cycle C_{2D}.  D = 2: K_{d,d}.
#    - D >= 3: arc-extended incidence graph of PG(2, q), saturated with spare
#      X-Y edges.  For d = 16 this is PG(2,13) plus a conic: 394 vertices.
#    - Early return if the base already meets the Moore bound.
# 2. Repair search (new): add a vertex pair (x in X, y in Y). Give each the
#    full degree d by transferring d edges (a,b) -> (x,b),(a,y). All degrees
#    are preserved, so the graph stays bipartite with max degree d. Then
#    anneal with degree-preserving 2-switches to drive the count of vertex
#    pairs at distance > D to zero. On success, keep the larger graph and
#    repeat. On failure, return the last verified graph.
# Every returned graph is checked with lib.is_valid, with the safe fallback
# used if the check fails.
# ----------------------------------------------------------------------------


def _key(u, v):
    return (u, v) if u < v else (v, u)


def _pg(q):
    """Return (m, incidence_edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    m = len(pts)
    _, inc = lib.projective_plane_incidence(q)
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in inc:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, inc, point_lines, line_points, index


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


def _greedy(m, s, point_lines, line_points, rng, trials, deadline):
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


def _conic(q, index, F):
    """Conic (plus nucleus for even q): an arc with q+1 (or q+2) points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, inc, pl, lp, S, d, rng):
    """Incidence graph of PG(2,q) plus a new A and B vertex per element of S, then saturated."""
    k = len(S)
    n = 2 * m + 2 * k
    E = set(_key(u, v) for u, v in inc)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in pl[P]:
            E.add(_key(x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.add(_key(Q, b))
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    X = list(range(m)) + list(range(2 * m, 2 * m + k))
    Y = list(range(m, 2 * m)) + list(range(2 * m + k, 2 * m + 2 * k))
    pairs = [(x, y) for x in X if deg[x] < d for y in Y if deg[y] < d]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d:
            continue
        key = _key(x, y)
        if key in E:
            continue
        E.add(key)
        deg[x] += 1
        deg[y] += 1
    return n, sorted(E)


def _arc_base(d, D, rng, deadline):
    """Best valid arc-extended PG(2,q) graph over prime powers q with q + 1 <= d, or None."""
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, inc, pl, lp, index = _pg(q)
        S = []
        if s >= 1:
            S = _greedy(m, s, pl, lp, rng, 30, deadline)
        if s >= 2:
            cs = _conic(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp) and len(cs) > len(S):
                S = cs
        if not _loads_ok(S, s, m, pl, lp):
            S = []
        n, E = _arc_graph(m, inc, pl, lp, S, d, rng)
        if best is None or n > best[0]:
            if lib.is_valid(n, E, d, D):
                best = (n, E)
    return best


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitmask BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _two_color(n, adj):
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


def _sa(n, adj, E, D, deadline, rng):
    """Anneal with degree-preserving 2-switches on X-Y edges until diameter <= D (cost 0) or time runs out."""
    cost = _bad_pairs(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    m = len(E)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 0.3 + 1.2 * max(0.0, 1.0 - (now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new = _bad_pairs(n, adj, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return cost


def _improve(n0, edges0, d, D, deadline, rng):
    """Repeatedly add a vertex pair by edge transfers and repair with annealing; return the best valid graph."""
    n = n0
    adj = [set() for _ in range(n)]
    for u, v in edges0:
        adj[u].add(v)
        adj[v].add(u)
    color = _two_color(n, adj)
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges0]
    best = (n0, list(edges0))

    while time.monotonic() < deadline:
        x = n
        y = n + 1
        adj.append(set())
        adj.append(set())
        color.append(0)  # x on the X side
        color.append(1)  # y on the Y side

        order = list(range(len(E)))
        rng.shuffle(order)
        used_a, used_b, picks = set(), set(), []
        for i in order:
            if len(picks) == d:
                break
            a, b = E[i]
            if a in used_a or b in used_b:
                continue
            used_a.add(a)
            used_b.add(b)
            picks.append(i)
        if len(picks) < d:
            break

        # Transfer: (a,b) -> (a,y) and (x,b). Degrees of a and b are unchanged.
        for i in picks:
            a, b = E[i]
            adj[a].discard(b); adj[b].discard(a)
            adj[a].add(y); adj[y].add(a)
            adj[x].add(b); adj[b].add(x)
            E[i] = (a, y)
            E.append((x, b))
        n += 2

        cost = _sa(n, adj, E, D, deadline, rng)
        if cost != 0:
            break
        edges = [(u, v) for u, v in E]
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
        else:
            break
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    moore = lib.moore_bound(d, D)
    base = _arc_base(d, D, rng, deadline)
    if base is None or not lib.is_valid(base[0], base[1], d, D):
        return fallback
    if base[0] >= moore:
        return base

    best = _improve(base[0], base[1], d, D, deadline, rng)
    if not lib.is_valid(best[0], best[1], d, D):
        return base if lib.is_valid(base[0], base[1], d, D) else fallback
    return best
