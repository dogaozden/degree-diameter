"""Bitset-reachability search for multi-base cyclic voltage lifts.

Construction: take k base vertices per side, a cyclic group Z_N and darts
(i, j, s) meaning A_{i,x} ~ B_{j,x+s}. Every base vertex has degree d, so the
lift is bipartite, d-regular and has 2kN vertices. Each base vertex's fibre is
one Python int bitmask, and voltage translation is a cyclic rotation of that
mask. A BFS step for a whole fibre therefore costs one shift-or per dart, and
the annealing search can evaluate far more candidates than per-vertex loops.
"""
import math
import random
import time

import lib

_BIG = 10 ** 9


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost(k, N, D, darts, FULL):
    """Number of (source, vertex) pairs not reached within D steps.

    darts: list of (i, j, s) meaning A_{i,x} ~ B_{j,x+s}. Zero means diameter <= D.
    Sources are the 2k base vertices; by translation symmetry of the lift, one
    representative per base vertex suffices.
    """
    fwd = darts
    bwd = [(j, i, (N - s) % N) for i, j, s in darts]
    total = 0
    for side in (0, 1):
        for b in range(k):
            RA = [0] * k
            RB = [0] * k
            if side == 0:
                RA[b] = 1
            else:
                RB[b] = 1
            FA = RA[:]
            FB = RB[:]
            for _ in range(D):
                NB = [0] * k
                for i, j, s in fwd:
                    x = FA[i]
                    if x:
                        NB[j] |= ((x << s) | (x >> (N - s))) & FULL
                NA = [0] * k
                for j, i, t in bwd:
                    x = FB[j]
                    if x:
                        NA[i] |= ((x << t) | (x >> (N - t))) & FULL
                alive = False
                nFA = [0] * k
                nFB = [0] * k
                for i in range(k):
                    f = NA[i] & ~RA[i]
                    nFA[i] = f
                    RA[i] |= f
                    if f:
                        alive = True
                for j in range(k):
                    f = NB[j] & ~RB[j]
                    nFB[j] = f
                    RB[j] |= f
                    if f:
                        alive = True
                FA, FB = nFA, nFB
                if not alive:
                    break
            total += 2 * k * N - sum(r.bit_count() for r in RA) - sum(r.bit_count() for r in RB)
    return total


def _edges(k, N, darts):
    """Expand darts into the simple bipartite graph on 2kN vertices."""
    E = []
    for i, j, s in darts:
        for x in range(N):
            E.append((i * N + x, (k + j) * N + (x + s) % N))
    return 2 * k * N, E


def _search(d, D, k, N, deadline, rng):
    """Anneal darts so that the lift has diameter <= D. Returns (n, edges) or None."""
    FULL = (1 << N) - 1
    kd = k * d
    A = [t // d for t in range(kd)]     # each A-base vertex used d times
    B = [t // d for t in range(kd)]     # each B-base vertex used d times
    rng.shuffle(B)
    S = [rng.randrange(N) for _ in range(kd)]

    def cost():
        darts = list(zip(A, B, S))
        if len(set(darts)) < kd:
            return _BIG
        return _cost(k, N, D, darts, FULL)

    cur = cost()
    T = 0.01
    while cur > 0 and time.monotonic() < deadline:
        t = rng.randrange(kd)
        if rng.random() < 0.7:
            old = S[t]
            S[t] = rng.randrange(N)
            if S[t] == old:
                continue
            c2 = cost()
            if c2 <= cur or rng.random() < T:
                cur = c2
            else:
                S[t] = old
        else:
            u = rng.randrange(kd)
            if B[t] == B[u]:
                continue
            B[t], B[u] = B[u], B[t]
            c2 = cost()
            if c2 <= cur or rng.random() < T:
                cur = c2
            else:
                B[t], B[u] = B[u], B[t]
    if cur == 0:
        return _edges(k, N, list(zip(A, B, S)))
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle: bipartite, 2-regular, diameter D
        return n, [(v, (v + 1) % n) for v in range(n)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    slice_t = max(1.0, 0.06 * budget)
    ks = [1, 2, 3, 4, 5, 6]
    while best[0] < moore and time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        k = rng.choice(ks)
        # Smallest fibre order N that makes 2kN beat the current best.
        base_min = best[0] // (2 * k) + 1
        if 2 * k * base_min > moore:
            continue
        N = base_min + rng.randrange(3)
        if 2 * k * N > moore:
            N = base_min
        if N < 2:
            continue
        t_end = min(deadline, time.monotonic() + min(remaining, slice_t))
        res = _search(d, D, k, N, t_end, rng)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
