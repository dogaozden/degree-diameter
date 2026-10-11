import math
import random
import time

import lib


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost(n, adj, D):
    """Number of ordered vertex pairs not within distance D (0 means diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _swap(adj, N, a1, b1, a2, b2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Side A is 0..N-1, side B is N..2N-1 in adj."""
    x1 = N + b1
    x2 = N + b2
    adj[a1][adj[a1].index(x1)] = x2
    adj[a2][adj[a2].index(x2)] = x1
    adj[x1][adj[x1].index(a1)] = a2
    adj[x2][adj[x2].index(a2)] = a1


def _sa_attempt(N, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on N+N vertices (starting from a Haar graph) to diameter <= D.

    Moves are degree-preserving double edge swaps. Returns (n, edges) on success, else None.
    """
    if N < d:
        return None
    shifts = rng.sample(range(N), d)
    E = [[i, (i + s) % N] for i in range(N) for s in shifts]
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    cost = _cost(n, adj, D)
    m = len(E)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = min(1.0, (now - t0) / span)
        T = 2.0 * (0.1 ** frac)
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or (N + b2) in adj[a1] or (N + b1) in adj[a2]:
            continue
        _swap(adj, N, a1, b1, a2, b2)
        c2 = _cost(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            E[i] = [a1, b2]
            E[j] = [a2, b1]
        else:
            _swap(adj, N, a1, b2, a2, b1)
    edges = [(a, N + b) for a, b in E]
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit

    if d < 1:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None and pg[0] > best_n and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
            best_n = pg[0]

    if D >= 3 and d >= 2:
        # Different family: direct edge-level annealing of a d-regular bipartite graph with N+N vertices.
        # Each success raises N by one; the first failure ends the search.
        rng = random.Random(seed * 7919 + d * 131 + D)
        N = max(best_n // 2 + 1, d)
        while time.monotonic() < deadline:
            res = _sa_attempt(N, d, D, rng, deadline)
            if res is None:
                break
            n, e = res
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
            N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
