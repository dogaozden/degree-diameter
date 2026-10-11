"""Bitset cyclic voltage-lift search for bipartite graphs with degree d and diameter D.

New routine: `_cost` evaluates a multi-base cyclic lift (k blocks per side, Z_N voltages,
d layers, each layer a permutation of the blocks) with big-integer shift-OR BFS. A block of
N bits is rotated by a voltage with two shifts, so one evaluation is a few hundred bigint
operations rather than a Python BFS over 2kN vertices. This gives far more annealing steps
per second. Annealing searches over voltages and layer permutations for every candidate
order just above the current best. Any found graph is checked with lib.is_valid.
"""
import math
import random
import time

import lib

BIG = 10 ** 9
SA_ITERS = 4000
SPAN = 60
KS = (1, 2, 3, 4)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost(k, N, d, D, M, perm, vol):
    """Number of (representative, vertex) pairs not within distance D. Zero means valid.

    Vertex A_{i,x} is adjacent to B_{j,x+s} for each dart (i, j, s) of each layer.
    Translations of Z_N act on both sides, so representatives A_{i,0} and B_{j,0} suffice.
    Bitset ints store the reached set of each block, and a shift by s moves all of them at once.
    """
    darts = []
    seen = set()
    for L in range(d):
        pl = perm[L]
        vl = vol[L]
        for i in range(k):
            j = pl[i]
            s = vl[i]
            key = (i, j, s)
            if key in seen:
                return BIG
            seen.add(key)
            darts.append((i, j, s, N - s))
    full = 2 * k * N
    total = 0
    reps = [(0, b) for b in range(k)] + [(1, b) for b in range(k)]
    for side, blk in reps:
        RA = [0] * k
        RB = [0] * k
        if side == 0:
            RA[blk] = 1
        else:
            RB[blk] = 1
        for _ in range(D):
            nA = RA[:]
            nB = RB[:]
            for i, j, s, sb in darts:
                x = RA[i]
                if x:
                    nB[j] |= ((x << s) | (x >> (N - s))) & M
                y = RB[j]
                if y:
                    nA[i] |= ((y << sb) | (y >> (N - sb))) & M
            RA, RB = nA, nB
        reached = 0
        for x in RA:
            reached += x.bit_count()
        for y in RB:
            reached += y.bit_count()
        total += full - reached
    return total


def _edges(k, N, d, perm, vol):
    """Build (n, edges) for the lift: A blocks first, then B blocks."""
    E = set()
    base_b = k * N
    for L in range(d):
        for i in range(k):
            j = perm[L][i]
            s = vol[L][i]
            for x in range(N):
                E.add((i * N + x, base_b + j * N + (x + s) % N))
    return 2 * k * N, sorted(E)


def _anneal(k, N, d, D, M, rng, end, iters):
    """Simulated annealing over voltages and layer permutations. Returns (perm, vol) or None."""
    perm = [rng.sample(range(k), k) for _ in range(d)]
    vol = [[rng.randrange(N) for _ in range(k)] for _ in range(d)]
    cost = _cost(k, N, d, D, M, perm, vol)
    T0, T1 = 6.0, 0.4
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() >= end:
            return None
        T = T0 * (T1 / T0) ** (it / iters)
        if k == 1 or rng.random() < 0.75:
            L = rng.randrange(d)
            i = rng.randrange(k)
            old = vol[L][i]
            new = rng.randrange(N)
            if new == old:
                continue
            vol[L][i] = new
            c2 = _cost(k, N, d, D, M, perm, vol)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                vol[L][i] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            p = perm[L]
            p[a], p[b] = p[b], p[a]
            c2 = _cost(k, N, d, D, M, perm, vol)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                p[a], p[b] = p[b], p[a]
    if cost == 0:
        return perm, vol
    return None


def _search_one(k, N, d, D, rng, end):
    """Random restarts of the annealer for one (k, N) until the time slice ends."""
    M = (1 << N) - 1
    while time.monotonic() < end:
        sol = _anneal(k, N, d, D, M, rng, end, SA_ITERS)
        if sol is not None:
            return sol
    return None


def _candidates(best_n, moore):
    """(n, k, N) with 2kN in (best_n, min(moore, best_n + SPAN)], sorted by n."""
    out = []
    hi = min(moore, best_n + SPAN)
    for k in KS:
        N = best_n // (2 * k) + 1
        while True:
            n = 2 * k * N
            if n > hi:
                break
            if N >= 2:
                out.append((n, k, N))
            N += 1
    out.sort()
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    slice_t = 0.4
    while best[0] < moore and time.monotonic() < deadline:
        cands = _candidates(best[0], moore)
        if not cands:
            break
        for n, k, N in cands[:12]:
            now = time.monotonic()
            if now >= deadline:
                break
            if n <= best[0]:
                continue
            end = min(deadline, now + slice_t)
            sol = _search_one(k, N, d, D, rng, end)
            if sol is not None:
                n2, e2 = _edges(k, N, d, sol[0], sol[1])
                consider(n2, e2)
        slice_t = min(slice_t * 1.5, 10.0)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
