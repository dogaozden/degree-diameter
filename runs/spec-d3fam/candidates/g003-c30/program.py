"""Degree-capped exchange annealing for bipartite diameter-D graphs.

Starting from a valid base graph, add one new vertex on each side (keeping
the bipartition) and anneal over the edge set with two moves: pick a
non-adjacent A-B pair, drop one random edge at each endpoint that is already
at degree d, and insert the new edge. Degrees never exceed d and the graph
stays bipartite. Cost = number of unordered pairs at distance > D. When the
cost reaches 0 the graph is kept and another pair of vertices is added.
"""
import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_base(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power, else None."""
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)
        except Exception:
            return None
    return None


def _colors_bfs(n, adj):
    """Bipartition of a bipartite graph given by adjacency sets."""
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


def _cost(n, adj, D):
    """Number of unordered vertex pairs at distance more than D."""
    edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return lib.bad_pairs(n, edges, D)


def _exchange_anneal(n0, edges0, d, D, deadline, rng):
    """Grow a valid graph by repeated vertex-pair insertion and degree-capped exchange annealing.

    Returns the largest valid (n, edges) found, or None if none beats the base.
    """
    adj = [set() for _ in range(n0)]
    for u, v in edges0:
        adj[u].add(v)
        adj[v].add(u)
    color = _colors_bfs(n0, adj)
    n = n0
    best = None
    cap = lib._moore_bound(d, D)

    while time.monotonic() < deadline and n + 2 <= cap:
        # One new vertex per side; the bipartition is preserved by every move.
        adj.append(set())
        adj.append(set())
        color.append(0)
        color.append(1)
        n += 2

        cur = _cost(n, adj, D)
        t0 = time.monotonic()
        span = max(1e-6, deadline - t0)
        while cur > 0 and time.monotonic() < deadline:
            frac = (time.monotonic() - t0) / span
            T = 0.8 * (0.02 ** frac)
            A = [v for v in range(n) if color[v] == 0]
            B = [v for v in range(n) if color[v] == 1]
            a = rng.choice(A)
            b = rng.choice(B)
            if b in adj[a]:
                continue
            removed = []
            for v in (a, b):
                if len(adj[v]) >= d:
                    u = rng.choice(sorted(adj[v]))
                    adj[v].discard(u)
                    adj[u].discard(v)
                    removed.append((v, u))
            adj[a].add(b)
            adj[b].add(a)
            c2 = _cost(n, adj, D)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                adj[a].discard(b)
                adj[b].discard(a)
                for v, u in removed:
                    adj[v].add(u)
                    adj[u].add(v)

        if cur != 0:
            break
        edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
        if not lib.is_valid(n, edges, d, D):
            break
        best = (n, edges)

    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        for cand in (_araujo_base(d), _best_pg(d)):
            if cand is not None:
                consider(cand[0], cand[1])

    # New family: exchange annealing grown from the best base, only when the
    # base is not already at the Moore bound.
    if D >= 3 and best_n < lib._moore_bound(d, D):
        res = _exchange_anneal(best_n, best[1], d, D, deadline, rng)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
