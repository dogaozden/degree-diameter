import math
import random
import time

import lib

BIG = 10 ** 9
ANNEAL_ITERS = 6000


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New helper: bitset rotation BFS for cyclic multi-base lifts.
#
# A cyclic lift with k base vertices per side over Z_N has vertices A_{i,x} and
# B_{j,x} (x in Z_N). A dart (i, j, s) joins A_{i,x} to B_{j,x+s}. The set of
# vertices reached on each base vertex is stored as an N-bit integer, so one
# BFS step over a dart is a cyclic rotation of a bitmask. This evaluates a
# candidate lift's unreached-pair count far faster than per-vertex lists.
# Translations by Z_N are automorphisms, so sources A_{i,0} and B_{j,0} suffice.
# ----------------------------------------------------------------------------

def _cost(k, N, D, darts, full):
    """Total number of (source, vertex) pairs not within distance D. darts: (i, j, s, (N-s) % N)."""
    twoN = 2 * k * N
    total = 0
    sources = [(0, i) for i in range(k)] + [(1, j) for j in range(k)]
    for side, src in sources:
        FA = [0] * k
        FB = [0] * k
        VA = [0] * k
        VB = [0] * k
        if side == 0:
            FA[src] = 1
            VA[src] = 1
        else:
            FB[src] = 1
            VB[src] = 1
        for _ in range(D):
            nA = [0] * k
            nB = [0] * k
            for i, j, sf, sb in darts:
                x = FA[i]
                if x:
                    nB[j] |= ((x << sf) | (x >> (N - sf))) & full
                y = FB[j]
                if y:
                    nA[i] |= ((y << sb) | (y >> (N - sb))) & full
            grew = False
            for i in range(k):
                v = nA[i] & ~VA[i]
                if v:
                    VA[i] |= v
                    grew = True
                nA[i] = v
            for j in range(k):
                v = nB[j] & ~VB[j]
                if v:
                    VB[j] |= v
                    grew = True
                nB[j] = v
            FA, FB = nA, nB
            if not grew:
                break
        visited = sum(x.bit_count() for x in VA) + sum(x.bit_count() for x in VB)
        total += twoN - visited
    return total


def _anneal_cyclic(d, D, k, N, rng, deadline, iters):
    """Anneal a d-regular bipartite base on k+k vertices, decomposed into d layers of
    permutations (König), with Z_N voltages. Returns (2kN, edges) if the lift has
    diameter <= D, else None."""
    full = (1 << N) - 1
    J = []   # J[L][i]: B-index matched to A_i in layer L
    S = []   # S[L][i]: voltage of that dart
    for _ in range(d):
        J.append(rng.sample(range(k), k))
        S.append([rng.randrange(N) for _ in range(k)])

    def cost_now():
        darts = []
        keys = set()
        for L in range(d):
            for i in range(k):
                s = S[L][i]
                j = J[L][i]
                key = (i, j, s)
                if key in keys:          # duplicate edges are forbidden
                    return BIG
                keys.add(key)
                darts.append((i, j, s, (N - s) % N))
        return _cost(k, N, D, darts, full)

    cur = cost_now()
    T0, T1 = 6.0, 0.3
    for t in range(iters):
        if cur == 0:
            break
        if (t & 31) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (t / iters)
        if k < 2 or rng.random() < 0.6:
            L = rng.randrange(d)
            i = rng.randrange(k)
            old = S[L][i]
            new = rng.randrange(N)
            if new == old:
                continue
            S[L][i] = new
            c2 = cost_now()
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                S[L][i] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            J[L][a], J[L][b] = J[L][b], J[L][a]
            c2 = cost_now()
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                J[L][a], J[L][b] = J[L][b], J[L][a]

    if cur != 0:
        return None
    E = []
    for L in range(d):
        for i in range(k):
            j = J[L][i]
            s = S[L][i]
            for x in range(N):
                E.append((i * N + x, k * N + j * N + (x + s) % N))
    return 2 * k * N, E


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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

    rng = random.Random(seed * 1000003 + 97 * d + D)
    ks = (2, 3, 4, 1, 5)
    attempt = 0
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        if all(2 * kk * (n_best // (2 * kk) + 1) > moore for kk in ks):
            break
        k = ks[attempt % len(ks)]
        attempt += 1
        N = n_best // (2 * k) + 1 + rng.randrange(3)
        if 2 * k * N > moore:
            continue
        res = _anneal_cyclic(d, D, k, N, rng, deadline, ANNEAL_ITERS)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
