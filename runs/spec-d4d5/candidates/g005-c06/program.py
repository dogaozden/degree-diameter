import math
import random
import time

import lib


def _bad_pairs_adj(N, adj, D):
    """Ordered pairs (v, w) with dist(v, w) > D, from bitmask reachability on adjacency lists."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _anneal_bipartite(n, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on n + n vertices by edge switches.

    Start from a Haar-type graph (union of d distinct cyclic shifts), then
    repeatedly swap the right endpoints of two random edges, which preserves
    all degrees and bipartiteness. Cost is the number of ordered pairs at
    distance > D. Returns a list of (left, right) pairs, or None on timeout.
    """
    if n < d:
        return None
    shifts = rng.sample(range(n), d)
    E = [[a, (a + s) % n] for s in shifts for a in range(n)]
    S = {(a, b) for a, b in E}
    N = 2 * n

    def cost_of(edges):
        adj = [[] for _ in range(N)]
        for a, b in edges:
            adj[a].append(n + b)
            adj[n + b].append(a)
        return _bad_pairs_adj(N, adj, D)

    c = cost_of(E)
    m = len(E)
    T0, T1 = 6.0, 0.3
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while c > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = min(1.0, (now - t0) / span)
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        E[i] = [a1, b2]
        E[j] = [a2, b1]
        c2 = cost_of(E)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S.discard((a1, b1))
            S.discard((a2, b2))
            S.add((a1, b2))
            S.add((a2, b1))
            c = c2
        else:
            E[i] = [a1, b1]
            E[j] = [a2, b2]
    return [(a, n + b) for a, b in E]


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and 2d vertices.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 2:
        return best_n, best_e

    try:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # Unstructured search: anneal d-regular bipartite graphs with a growing side size n.
        n = max(d, best_n // 2 + 1)
        fails = 0
        while True:
            rem = end - time.monotonic()
            if rem < 0.5:
                break
            budget = max(0.5, rem * 0.5)
            res = _anneal_bipartite(n, d, D, rng, time.monotonic() + budget)
            if res is not None:
                edges = res
                consider(2 * n, edges)
                n += max(1, n // 20)
                fails = 0
            else:
                fails += 1
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
