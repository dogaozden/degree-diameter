import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases.
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


# ----------------------------------------------------------------------------
# Deficit-chasing annealed vertex insertion (diameter-constrained rewiring).
#
# Idea: take a valid graph on n vertices and add one new vertex on each side.
# The new vertices start isolated. Repeatedly pick a random cross pair (u, v)
# that is not an edge. If u or v is saturated (degree d), first delete one of
# its random edges, which pushes the deficit onto the old neighbour. Then add
# (u, v). Accept or reject by Metropolis on the number of vertex pairs at
# distance > D. Adding edges never increases that count, so the search only
# moves toward a valid graph on n+2 vertices when it can find one.
# ----------------------------------------------------------------------------

def _bad_pairs_adj(n, adjs, D):
    """Number of unordered vertex pairs at distance > D, from set-based adjacency."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adjs[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal_insert(n, color, d, D, base_edges, deadline, rng, T0, T1):
    """Search for a valid graph on n vertices (degree <= d, bipartition `color`) with base_edges inside.

    Returns the edge list on success, or None if the deadline passes first.
    """
    adjs = [set() for _ in range(n)]
    for u, v in base_edges:
        adjs[u].add(v)
        adjs[v].add(u)
    side = [[v for v in range(n) if color[v] == c] for c in (0, 1)]
    cur = _bad_pairs_adj(n, adjs, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)

    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** ((now - t0) / span)

        u = rng.randrange(n)
        v = rng.choice(side[1 - color[u]])
        if v in adjs[u]:
            continue

        ops = []
        if len(adjs[u]) >= d:
            w = rng.choice(list(adjs[u]))
            adjs[u].discard(w)
            adjs[w].discard(u)
            ops.append((0, u, w))
        if len(adjs[v]) >= d:
            w = rng.choice(list(adjs[v]))
            adjs[v].discard(w)
            adjs[w].discard(v)
            ops.append((0, v, w))
        adjs[u].add(v)
        adjs[v].add(u)
        ops.append((1, u, v))

        new = _bad_pairs_adj(n, adjs, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            for kind, a, b in reversed(ops):
                if kind == 1:
                    adjs[a].discard(b)
                    adjs[b].discard(a)
                else:
                    adjs[a].add(b)
                    adjs[b].add(a)

    if cur != 0:
        return None
    return [(u, v) for u in range(n) for v in adjs[u] if u < v]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
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

    if D >= 3:
        # Araujo-Pardo & Lopez record family for d = q + 2, q a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                consider(n_a, e_a)
            except Exception:
                pass
        pg = _pg_base(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # New stage: grow the best D = 3 graph by two vertices (one per side) via
    # deficit-chasing annealing, repeating while successful.
    if D == 3 and best_n < lib._moore_bound(d, D):
        base_edges = list(best[1])
        adj = [[] for _ in range(best_n)]
        for u, v in base_edges:
            adj[u].append(v)
            adj[v].append(u)
        color = _bipartition(best_n, adj)

        while time.monotonic() < deadline:
            n_new = best_n + 2
            if n_new > lib._moore_bound(d, D):
                break
            cols = color + [0, 1]
            res = _anneal_insert(n_new, cols, d, D, base_edges, deadline,
                                 rng, 3.0, 0.1)
            if res is None or not lib.is_valid(n_new, res, d, D):
                break
            best = (n_new, res)
            best_n = n_new
            base_edges = res
            color = cols

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
