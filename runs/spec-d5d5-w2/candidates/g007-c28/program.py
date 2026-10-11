import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy:
#   1. Safe baselines: K_{d,d} (any D >= 2) and the projective-plane incidence
#      graph PG(2, q) (any D >= 3, degree q+1 <= d).
#   2. Bold change: a bipartite simulated-annealing search that does not use any
#      group structure. Start from a d-regular bipartite Haar graph on N + N
#      vertices (N just above the current record half-order). Apply degree-
#      preserving double-edge swaps and minimise the number of ordered vertex
#      pairs at distance greater than D. Cost zero means the graph is valid.
#   3. Every candidate is checked with lib.is_valid before it can replace the
#      best graph, so the output is always valid.
# ----------------------------------------------------------------------------

_TEMP_END = 0.3


def _bip_cost(n, nbr, D):
    """Number of ordered vertex pairs at distance greater than D (0 means diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal(N, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on N + N vertices until its diameter is <= D.

    Returns the edge list (A-vertex a in 0..N-1, B-vertex b in N..2N-1), or None on timeout.
    """
    n = 2 * N
    shifts = rng.sample(range(N), d)
    E = [(i, N + (i + s) % N) for i in range(N) for s in shifts]
    Eset = set(E)
    nbr = [[] for _ in range(n)]
    for a, b in E:
        nbr[a].append(b)
        nbr[b].append(a)
    cost = _bip_cost(n, nbr, D)
    if cost == 0:
        return E

    T0 = max(2.0, 0.01 * cost)
    T1 = _TEMP_END
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    M = len(E)

    while True:
        now = time.monotonic()
        if now >= deadline:
            return None
        temp = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)

        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in Eset or (a2, b1) in Eset:
            continue

        # Double-edge swap: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Degrees are preserved.
        nbr[a1].remove(b1)
        nbr[b1].remove(a1)
        nbr[a2].remove(b2)
        nbr[b2].remove(a2)
        nbr[a1].append(b2)
        nbr[b2].append(a1)
        nbr[a2].append(b1)
        nbr[b1].append(a2)

        new = _bip_cost(n, nbr, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = new
            Eset.discard((a1, b1))
            Eset.discard((a2, b2))
            Eset.add((a1, b2))
            Eset.add((a2, b1))
            E[i] = (a1, b2)
            E[j] = (a2, b1)
            if cost == 0:
                return E
        else:
            # Revert the swap.
            nbr[a1].remove(b2)
            nbr[b2].remove(a1)
            nbr[a2].remove(b1)
            nbr[b1].remove(a2)
            nbr[a1].append(b1)
            nbr[b1].append(a1)
            nbr[a2].append(b2)
            nbr[b2].append(a2)


def _pg_baseline(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and meets the Moore bound for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    if D >= 3:
        pg = _pg_baseline(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

    # Bold search: simulated annealing over unstructured bipartite graphs.
    if d >= 2:
        rng = random.Random(seed * 1000003 + 97 * d + D)
        N = best[0] // 2 + 1
        while time.monotonic() < deadline - 0.5 and 2 * N <= moore and N > d:
            now = time.monotonic()
            remaining = deadline - now
            slice_end = now + max(3.0, 0.5 * remaining)
            E = _anneal(N, d, D, rng, min(deadline, slice_end))
            if E is not None:
                n = 2 * N
                e = [(a, b) for a, b in E]
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
