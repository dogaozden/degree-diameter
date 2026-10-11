import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baseline: incidence graph of PG(2, q) (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW construction: random bipartite d-regular graph repaired by edge switches.
#
# Each side has N vertices, A = 0..N-1 and B = N..2N-1. Edge e = a*d + s joins
# A-vertex a to B-vertex EB[e]. The B-side slot of edge e is TB[e].
# Start: d random permutations (a random d-regular bipartite multigraph).
# Move: switch two edges (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). This keeps every
# degree fixed and the graph bipartite. Cost = unreached pairs at distance > D
# plus a penalty for duplicate edges. Simulated annealing runs until cost 0.
# Each attempt uses a bitset BFS in numpy: reach[v] is a bit-row over all vertices.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_PEN = 40.0


def _cost(n, nb, D, W):
    """Number of unordered vertex pairs at distance > D, from packed bitset BFS."""
    reach = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[nb], axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    pc = int(_POP8[reach.view(np.uint8)].sum())
    return (n * n - pc) // 2


def _attempt(d, D, N, rng, deadline):
    """Simulated annealing for a d-regular bipartite graph on 2N vertices with diameter <= D.

    Returns (n, edges) on success, or None if the deadline passes first.
    """
    E = N * d
    n = 2 * N
    W = (n + 63) // 64
    gen = np.random.default_rng(rng.randrange(1 << 31))

    EB = np.empty(E, dtype=np.int64)     # B endpoint of edge e (A endpoint is e // d)
    for s in range(d):
        EB[s::d] = gen.permutation(N)
    TB = np.tile(np.arange(d, dtype=np.int64), N)   # slot of edge e on the B side
    nbrB = np.empty((N, d), dtype=np.int64)
    nbrB[EB, TB] = np.repeat(np.arange(N, dtype=np.int64), d)

    M = np.zeros((N, N), dtype=np.int64)
    np.add.at(M, (np.repeat(np.arange(N, dtype=np.int64), d), EB), 1)
    dup = int(np.maximum(M - 1, 0).sum())

    def full_nb():
        return np.concatenate([EB.reshape(N, d) + N, nbrB])

    def switch(e1, e2):
        # Replace (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Applying it twice undoes it.
        nonlocal dup
        a1 = e1 // d
        a2 = e2 // d
        b1 = int(EB[e1])
        b2 = int(EB[e2])
        t1 = int(TB[e1])
        t2 = int(TB[e2])
        if M[a1, b1] >= 2:
            dup -= 1
        M[a1, b1] -= 1
        if M[a2, b2] >= 2:
            dup -= 1
        M[a2, b2] -= 1
        if M[a1, b2] >= 1:
            dup += 1
        M[a1, b2] += 1
        if M[a2, b1] >= 1:
            dup += 1
        M[a2, b1] += 1
        EB[e1] = b2
        EB[e2] = b1
        TB[e1] = t2
        TB[e2] = t1
        nbrB[b2, t2] = a1
        nbrB[b1, t1] = a2

    cost = _cost(n, full_nb(), D, W) + _PEN * dup
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)

    while cost > 0:
        now = time.monotonic()
        if now > deadline:
            return None
        frac = (now - t0) / span
        T = 1.5 * (1.0 - frac) + 0.05
        e1 = rng.randrange(E)
        e2 = rng.randrange(E)
        if e1 // d == e2 // d or EB[e1] == EB[e2]:
            continue
        switch(e1, e2)
        c2 = _cost(n, full_nb(), D, W) + _PEN * dup
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            switch(e1, e2)

    if dup != 0:
        return None
    edges = [(a, N + int(EB[a * d + s])) for a in range(N) for s in range(d)]
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact calibration path: PG(2,q) gives the record for D = 3 when d-1 is a prime power.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if d < 3:
        return best

    # Per-side Moore size for a bipartite graph with max degree d and diameter D.
    moore_side = max(d, lib._moore_bound(d, D) // 2)
    N = max(d, int(0.36 * moore_side))
    step = max(1, N // 60)
    bestN = 0

    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 1.0:
            break
        slice_end = min(deadline, now + max(2.0, remaining * 0.45))
        if N < d:
            N = d
        res = None
        try:
            res = _attempt(d, D, N, rng, slice_end)
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])
            bestN = max(bestN, N)
            N = N + step
        else:
            if bestN:
                N = bestN + max(1, (N - bestN) // 2)
            else:
                N = max(d, N - step)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
