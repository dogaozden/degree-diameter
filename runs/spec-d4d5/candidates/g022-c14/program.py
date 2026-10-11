import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane baseline (diameter 3, optimal when d-1 is a prime power).
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Return (q, (n, edges)) for the incidence graph of PG(2, q), q the largest prime power with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q, lib.projective_plane_incidence(q)
    return None, None


# ----------------------------------------------------------------------------
# New family: bipartite double-edge-switch annealing on the bad-pair count.
#
# Start from a d-regular bipartite circulant on N + N vertices (A = 0..N-1,
# B = N..2N-1, a_i ~ b_{(i+s) mod N} for s < d). Each move is a double-edge
# switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keeps every degree equal to d,
# keeps the graph bipartite and never creates a multi-edge. The cost is the
# number of vertex pairs at distance > D. Unlike the group-lift family, this
# search is not tied to any group structure.
# ----------------------------------------------------------------------------

def _adj(N, E):
    """Adjacency lists of the bipartite graph with A = 0..N-1 and B = N..2N-1 from pairs (a, b)."""
    adj = [[] for _ in range(2 * N)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    return adj


def _bad_pairs_fast(n, adj, D):
    """Number of unordered pairs at distance > D, via bitmask ball expansion."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _switch_anneal(N, d, D, rng, deadline, iters):
    """Anneal double-edge switches from a circulant start; return (N, pairs) on success, else None."""
    M = N * d
    E = [(i, (i + s) % N) for i in range(N) for s in range(d)]
    S = set(E)

    def try_switch(i, j):
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            return None
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in S or n2 in S:
            return None
        return (a1, b1), (a2, b2), n1, n2

    def apply(i, j, o1, o2, n1, n2):
        # Replace pairs o1, o2 (at positions i, j) by n1, n2.
        S.discard(o1)
        S.discard(o2)
        S.add(n1)
        S.add(n2)
        E[i] = n1
        E[j] = n2

    # Mix the circulant so the start is not structured.
    for _ in range(3 * M):
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        r = try_switch(i, j)
        if r is not None:
            apply(i, j, *r)

    n = 2 * N
    cost = _bad_pairs_fast(n, _adj(N, E), D)
    T0 = 2.0
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        r = try_switch(i, j)
        if r is None:
            continue
        old1, old2, n1, n2 = r
        apply(i, j, old1, old2, n1, n2)
        c2 = _bad_pairs_fast(n, _adj(N, E), D)
        delta = c2 - cost
        T = T0 * (1.0 - it / max(1, iters)) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            apply(i, j, n1, n2, old1, old2)  # undo

    if cost == 0:
        return N, list(E)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Projective plane baseline; exact optimum for D = 3 when d - 1 is a prime power.
    q, pg = _pg_candidate(d)
    if pg is not None:
        consider(pg[0], pg[1])
        if D == 3 and q == d - 1:
            if lib.is_valid(best[0], best[1], d, D):
                return best

    # Main search: bipartite switch annealing, targeting N per side with 2N > best_n.
    if d >= 3:
        N = max(d, best_n // 2 + 1)
        while time.monotonic() < deadline:
            res = _switch_anneal(N, d, D, rng, deadline, iters=4000)
            if res is not None:
                NN, E = res
                edges = [(a, NN + b) for a, b in E]
                consider(2 * NN, edges)
                N = NN + 1  # aim one step higher after each success
            # on failure: restart at the same N from a fresh circulant

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
