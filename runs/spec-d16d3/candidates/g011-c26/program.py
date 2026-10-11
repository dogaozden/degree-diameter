import math
import random
import time

import lib


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _conic(q, index, F):
    """Conic (plus nucleus for even q) as a set of point indices."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _twin_base(d):
    """PG(2,q) incidence plus twin vertices on a conic (valid diameter 3). Returns (n, edges) or None."""
    q = _largest_prime_power_le(min(d - 1, 23))
    if q is None:
        return None
    s = d - q - 1
    n2, pedges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in pedges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    S = []
    if s >= 2:
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        F = lib.GF(q)
        cand = _conic(q, index, F)
        if _loads_ok(cand, s, m, point_lines, line_points):
            S = cand
    edges = list(pedges)
    n = n2
    k = len(S)
    if k:
        for t, P in enumerate(S):
            x = n2 + t
            for L in point_lines[P]:
                edges.append((x, m + L))
        for t, j in enumerate(S):
            b = n2 + k + t
            for Q in line_points[j]:
                edges.append((Q, b))
        n = n2 + 2 * k
    return n, edges


def _bipartition(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _cost(n, adj):
    """Number of unordered pairs at distance > 3 (zero iff diameter <= 3)."""
    ball = [1 << v for v in range(n)]
    for _ in range(3):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(n, adj, col, d, side, rng):
    """Append a vertex on `side` adjacent to <= d spare opposite-side vertices, greedily covering."""
    pool = [y for y in range(n) if col[y] != side and len(adj[y]) < d]
    if not pool:
        return None
    covered = set()
    chosen = []
    for _ in range(d):
        if not pool:
            break
        best_i, best_key = 0, -1.0
        for i, y in enumerate(pool):
            key = len(adj[y] - covered) + rng.random() * 0.99
            if key > best_key:
                best_key, best_i = key, i
        y = pool.pop(best_i)
        chosen.append(y)
        covered |= adj[y]
    v = n
    adj.append(set(chosen))
    col.append(side)
    for y in chosen:
        adj[y].add(v)
    return n + 1


def _anneal(n, adj, col, d, deadline, rng, iters):
    """Edge-endpoint moves under simulated annealing; returns True if cost reaches 0."""
    cost = _cost(n, adj)
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.03 ** (it / iters))
        a = rng.randrange(n)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = -1
        for _ in range(40):
            x = rng.randrange(n)
            if col[x] != col[a] and x != b and x not in adj[a] and len(adj[x]) < d:
                c = x
                break
        if c < 0:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(c)
        adj[c].add(a)
        new = _cost(n, adj)
        u = 1.0 - rng.random()
        if new <= cost - T * math.log(u):
            cost = new
        else:
            adj[a].discard(c)
            adj[c].discard(a)
            adj[a].add(b)
            adj[b].add(a)
    return cost == 0


def _extend(n, edges, d, D, deadline, rng):
    """Repeatedly try to add one vertex and repair by annealing; keep only valid growth."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _bipartition(n, adj)
    best = (n, edges)
    while time.monotonic() < deadline:
        if all(len(a) >= d for a in adj):
            break
        side = rng.randrange(2)
        c_adj = [set(a) for a in adj]
        c_col = list(col)
        c_n = _add_vertex(n, c_adj, c_col, d, side, rng)
        if c_n is None:
            continue
        if not _anneal(c_n, c_adj, c_col, d, deadline, rng, 800):
            continue
        new_edges = [(u, v) for u in range(c_n) for v in c_adj[u] if u < v]
        if lib.is_valid(c_n, new_edges, d, D):
            n, adj, col = c_n, c_adj, c_col
            best = (n, new_edges)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.7 * time_limit)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    fallback = lib.haar_graph(d, range(d))
    if D != 3:
        return fallback

    rng = random.Random(seed)
    best = fallback
    base = _twin_base(d)
    if base is not None:
        n, edges = base
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best = _extend(best[0], best[1], d, D, deadline, rng)

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
