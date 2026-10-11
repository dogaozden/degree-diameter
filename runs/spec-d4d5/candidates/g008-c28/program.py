import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (or None)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _reach_masks(n, adj, D):
    """Bitmask per vertex of all vertices within distance D (BFS-by-bitset)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        changed = False
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            if r != reach[v]:
                changed = True
            new.append(r)
        reach = new
        if not changed:
            break
    return reach


def _cost_of(h, D, es):
    """Number of ordered (vertex, vertex) pairs at distance > D in the bipartite graph with edges (a, b).

    Side A is vertices 0..h-1, side B is vertices h..2h-1 (B index b maps to h + b).
    """
    n = 2 * h
    adj = [[] for _ in range(n)]
    for a, b in es:
        adj[a].append(h + b)
        adj[h + b].append(a)
    reach = _reach_masks(n, adj, D)
    return sum(n - r.bit_count() for r in reach)


def _anneal(h, d, D, rng, t_end):
    """Simulated annealing over d-regular bipartite graphs on h + h vertices.

    State: edge list with d*h edges, every vertex of degree exactly d.
    Move: 2-switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keeps regularity and bipartiteness.
    Cost: number of ordered pairs farther than D apart. Returns an edge list (a, b) with cost 0, or None.
    """
    shifts = rng.sample(range(h), d)
    edges = [[a, (a + s) % h] for s in shifts for a in range(h)]
    eset = set((a, b) for a, b in edges)
    m = len(edges)

    cur = _cost_of(h, D, edges)
    if cur == 0:
        return [(a, b) for a, b in edges]

    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    T0, T1 = 3.0, 0.15

    while True:
        now = time.monotonic()
        if now >= t_end:
            return None
        frac = (now - t0) / span
        T = T0 * (T1 / T0) ** frac

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = edges[i]
        a2, b2 = edges[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue

        edges[i] = [a1, b2]
        edges[j] = [a2, b1]
        new_c = _cost_of(h, D, edges)
        delta = new_c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            eset.discard((a1, b1))
            eset.discard((a2, b2))
            eset.add((a1, b2))
            eset.add((a2, b1))
            cur = new_c
            if cur == 0:
                return [(a, b) for a, b in edges]
        else:
            edges[i] = [a1, b1]
            edges[j] = [a2, b2]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 2.0)
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

    moore = lib._moore_bound(d, D)

    # Projective plane base (diameter 3, valid for every D >= 3).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if best_n >= moore:
        return best

    # Main search: annealed bipartite d-regular graphs with growing side size h.
    h = max(d, best_n // 2 + 1)
    while time.monotonic() < deadline and best_n < moore:
        remaining = deadline - time.monotonic()
        budget = min(remaining, max(2.0, 0.5 * remaining))
        es = _anneal(h, d, D, rng, time.monotonic() + budget)
        if es is not None:
            n = 2 * h
            e = [(a, h + b) for a, b in es]
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
            h = max(h + 1, h + max(1, h // 25))
        # On failure keep the same h and restart with a fresh random start.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
