"""Cyclic-start annealing with bitset diameter cost, plus a safe Haar fallback.

Construction (different from the parent's bi-Cayley / multi-base voltage search):
  * Start from a Haar graph H(N, S), a d-regular bipartite circulant on 2N vertices.
  * Repair it by degree-preserving double-edge swaps between the two sides,
    annealing on the number of vertex pairs at distance > D. Distances are
    computed for all vertices at once with big-int bitset balls.
  * Ladder over N: grow N while annealing succeeds, shrink the step when it fails.
Every accepted graph is checked with lib.is_valid. The fallback is K_{d,d}.
"""
import math
import random
import time

import lib


def _cost(N, D, E):
    """Number of ordered vertex pairs at distance > D (0 means diameter <= D and connected)."""
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nb = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb.append(x)
        ball = nb
    return sum(n - x.bit_count() for x in ball)


def _anneal(N, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on N+N vertices toward diameter <= D.

    Returns the list of (a, b) pairs (a, b in 0..N-1) on success, else None.
    """
    S = rng.sample(range(N), d)
    E = [(x, (x + s) % N) for x in range(N) for s in S]
    eset = set(E)
    cost = _cost(N, D, E)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = max(0.15, 1.5 * (1.0 - (now - t0) / span))
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        # Double-edge swap: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Degrees are preserved.
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        eset.discard((a1, b1))
        eset.discard((a2, b2))
        eset.add((a1, b2))
        eset.add((a2, b1))
        c2 = _cost(N, D, E)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            eset.discard((a1, b2))
            eset.discard((a2, b1))
            eset.add((a1, b1))
            eset.add((a2, b2))
    return E


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 6.0))
    deadline = t_start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: bipartite, degree d, diameter 2. Safe fallback for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best[0], best[1]

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best[0], best[1]

    # Exact incidence graph of PG(2, d-1) meets the Moore bound for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    rng = random.Random(seed)
    Nmax = moore // 2
    lo = d          # Haar graph with N = d is K_{d,d}, which is valid
    step = 1

    while True:
        remaining = deadline - time.monotonic()
        if remaining < 0.5 or step < 1 or lo >= Nmax:
            break
        N = min(lo + step, Nmax)
        if N <= lo:
            break
        slice_end = min(deadline, time.monotonic() + max(0.5, 0.3 * remaining))
        E = _anneal(N, d, D, rng, slice_end)
        if E is not None:
            consider(2 * N, [(a, N + b) for a, b in E])
            lo = N
            step *= 2
        else:
            step //= 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], best[1]
