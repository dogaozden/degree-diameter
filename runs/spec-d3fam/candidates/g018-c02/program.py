import math
import random
import time

import lib


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency collections."""
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


def _cost(adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included). Zero means valid."""
    n = len(adj)
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt.append(x)
        ball = nxt
    return sum(n - b.bit_count() for b in ball) // 2


def _to_edges(adj, side):
    return [(u, v) for u in range(len(adj)) if side[u] == 0 for v in adj[u]]


def _anneal_extend(d, D, adj, side, deadline, rng, record):
    """Simulated annealing over bipartite graphs with degree <= d.

    Moves insert a random non-adjacent left-right pair; if an endpoint is saturated,
    a random incident edge is removed first (a rewire). When the cost reaches zero the
    current graph is recorded and one left and one right vertex are added.
    """
    L_ids = [v for v in range(len(adj)) if side[v] == 0]
    R_ids = [v for v in range(len(adj)) if side[v] == 1]

    def add_pair():
        x = len(adj)
        adj.append(set())
        side.append(0)
        L_ids.append(x)
        adj.append(set())
        side.append(1)
        R_ids.append(x + 1)

    cur = _cost(adj, D)
    it = 0
    while time.monotonic() < deadline:
        if cur == 0:
            record(adj, side)
            add_pair()
            cur = _cost(adj, D)
            it = 0
            continue
        it += 1
        T = max(0.2, 2.0 * math.exp(-it / 1500.0))
        a = rng.choice(L_ids)
        b = rng.choice(R_ids)
        if b in adj[a]:
            continue
        undo = []
        if len(adj[a]) >= d:
            x = rng.choice(tuple(adj[a]))
            adj[a].discard(x)
            adj[x].discard(a)
            undo.append((a, x))
        if len(adj[b]) >= d:
            y = rng.choice(tuple(adj[b]))
            adj[b].discard(y)
            adj[y].discard(b)
            undo.append((y, b))
        adj[a].add(b)
        adj[b].add(a)
        new = _cost(adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            adj[a].discard(b)
            adj[b].discard(a)
            for u, v in undo:
                adj[u].add(v)
                adj[v].add(u)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Moore-optimal case for D = 3: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    if D >= 3:
        # Araujo-Pardo & Lopez record family when d-2 is a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except (ValueError, StopIteration, KeyError):
                pass
        # Plain projective plane with the largest prime power q <= d-1.
        q = next((q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)), None)
        if q is not None:
            consider(*lib.projective_plane_incidence(q))

    # Main search: annealed bipartite edge-rewiring, growing one vertex pair at a time.
    n0, e0 = best
    adj = [set() for _ in range(n0)]
    for u, v in e0:
        adj[u].add(v)
        adj[v].add(u)
    side = _bipartition(n0, adj)

    def record(adj_, side_):
        nonlocal best
        n = len(adj_)
        if n > best[0]:
            e = _to_edges(adj_, side_)
            if lib.is_valid(n, e, d, D):
                best = (n, e)

    _anneal_extend(d, D, adj, side, deadline, rng, record)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
