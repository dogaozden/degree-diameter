"""Voltage lifts of projective-plane incidence graphs (cyclic groups Z_M).

Base graph: incidence graph of PG(2, q), q the largest prime power with q <= d-1.
It is q+1 regular with diameter 3, so every Z_M lift keeps degree q+1 and bipartiteness.
A lift has nb * M vertices. We anneal the voltages on the non-tree edges (a spanning
tree is gauged to voltage 0) to minimise the number of ordered pairs at distance > D.
M increases while lifts succeed. Every candidate is checked with lib.is_valid before
it is kept, and a valid fallback is always returned.
"""
import math
import random
import time

import lib


SLICE = 8.0  # seconds of annealing per attempt at a given lift order


def _largest_prime_power_at_most(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _spanning_tree_edges(nb, E):
    """Indices of the edges of a BFS spanning tree of the base graph (connected)."""
    adj = [[] for _ in range(nb)]
    for idx, (u, v) in enumerate(E):
        adj[u].append((v, idx))
        adj[v].append((u, idx))
    seen = [False] * nb
    seen[0] = True
    tree = set()
    stack = [0]
    while stack:
        u = stack.pop()
        for v, idx in adj[u]:
            if not seen[v]:
                seen[v] = True
                tree.add(idx)
                stack.append(v)
    return tree


def _lift_adj(nb, E, a, M):
    """Adjacency lists of the Z_M lift; dart (u, v, s) joins u*M+g to v*M+(g+s)%M."""
    N = nb * M
    adj = [[] for _ in range(N)]
    for (u, v), s in zip(E, a):
        ub = u * M
        vb = v * M
        for g in range(M):
            x = ub + g
            y = vb + (g + s) % M
            adj[x].append(y)
            adj[y].append(x)
    return N, adj


def _pair_cost(N, adj, D):
    """Number of ordered (vertex, vertex) pairs at distance > D (0 means diameter <= D)."""
    ball = [1 << x for x in range(N)]
    for _ in range(D):
        new = []
        for x in range(N):
            r = ball[x]
            for y in adj[x]:
                r |= ball[y]
            new.append(r)
        ball = new
    return sum(N - b.bit_count() for b in ball)


def _anneal(nb, E, M, D, free, deadline, rng):
    """Anneal the free voltages so the Z_M lift has diameter <= D. Returns voltages or None."""
    if not free or M < 2:
        return None
    a = [0] * len(E)
    for i in free:
        a[i] = rng.randrange(M)
    N, adj = _lift_adj(nb, E, a, M)
    cur = _pair_cost(N, adj, D)
    T = 3.0
    while cur > 0 and time.monotonic() < deadline:
        T = max(0.3, T * 0.997)
        idx = rng.choice(free)
        old = a[idx]
        new = rng.randrange(M - 1)
        if new >= old:
            new += 1
        a[idx] = new
        N, adj = _lift_adj(nb, E, a, M)
        c2 = _pair_cost(N, adj, D)
        limit = cur - T * math.log(1.0 - rng.random())  # log argument in (0, 1]
        if c2 <= limit:
            cur = c2
        else:
            a[idx] = old
    return a if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Moore bound for bipartite graphs (d >= 3): stop once it is met.
    if d >= 3:
        moore = 2 * sum((d - 1) ** i for i in range(D))
        if best_n >= moore:
            return best

    if D >= 3:
        q = _largest_prime_power_at_most(d - 1)
        if q is not None:
            nb, E = lib.projective_plane_incidence(q)
            E = [(u, v) for u, v in E]
            consider(nb, E)
            tree = _spanning_tree_edges(nb, E)
            free = [i for i in range(len(E)) if i not in tree]
            M = max(2, best_n // nb + 1)
            while time.monotonic() < deadline:
                if d >= 3 and best_n >= 2 * sum((d - 1) ** i for i in range(D)):
                    break
                slice_end = min(deadline, time.monotonic() + SLICE)
                a = _anneal(nb, E, M, D, free, slice_end, rng)
                if a is not None:
                    darts = [(u, v, s) for (u, v), s in zip(E, a)]
                    n, e = lib.voltage_lift(nb, darts, M)
                    consider(n, e)
                    M += 1
                # On failure the same M is retried with a fresh random start.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
