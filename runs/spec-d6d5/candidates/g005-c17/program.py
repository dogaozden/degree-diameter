import math
import random
import time

import lib


_BIG = 10 ** 9


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Orbit-bitset evaluator for Z_m voltage lifts (new in this version).
#
# Base graph: k A-vertices and k B-vertices. A dart (i, j, s) joins A_{i,g} to
# B_{j,g+s} for every g in Z_m. Translation by any t is an automorphism, so each
# base class is one orbit. Therefore the lift has diameter <= D iff, for each of
# the 2k base representatives, the radius-D ball covers its whole class.
#
# Each class is kept as a Python-int bitset over Z_m. Moving a set across a dart
# is a cyclic bit rotation, so one BFS layer costs O(#darts) big-int operations.
# This is much faster than explicit BFS on the lifted graph, which lets the
# annealer test many voltage vectors per second.
# ----------------------------------------------------------------------------

def _cost(m, k, D, darts):
    """Number of (source representative, class element) pairs missed by radius D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG  # duplicate darts would create duplicate edges
    full = (1 << m) - 1
    sh = [(i, j, s, (m - s) % m) for i, j, s in darts]

    def rot(X, t):
        if t == 0:
            return X
        return ((X << t) | (X >> (m - t))) & full

    total = 0
    sources = [(0, i) for i in range(k)] + [(1, j) for j in range(k)]
    for side, idx in sources:
        A = [0] * k
        B = [0] * k
        if side == 0:
            A[idx] = 1
        else:
            B[idx] = 1
        for _ in range(D):
            nA = A[:]
            nB = B[:]
            for i, j, s, si in sh:
                if A[i]:
                    nB[j] |= rot(A[i], s)
                if B[j]:
                    nA[i] |= rot(B[j], si)
            A, B = nA, nB
        for x in A:
            total += m - x.bit_count()
        for x in B:
            total += m - x.bit_count()
    return total


def _random_darts(m, k, d, rng):
    """d layers, each a random permutation p of range(k); dart l*k+i is [i, p[i], voltage]."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(m)])
    return darts


def _anneal(m, k, d, D, rng, iters, deadline):
    """Simulated annealing over voltages and layer permutations. Returns darts or None."""
    darts = _random_darts(m, k, d, rng)
    cost = _cost(m, k, D, darts)
    T0 = 4.0
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.1
        old = [x[:] for x in darts]
        if k == 1 or rng.random() < 0.75:
            idx = rng.randrange(len(darts))
            darts[idx][2] = rng.randrange(m)
        else:
            # Swap the targets of two darts in one layer (keeps each layer a permutation).
            l = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = l * k + a, l * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
        c2 = _cost(m, k, D, darts)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            darts = old
    return darts if cost == 0 else None


def _edges(m, k, darts):
    """Lift the darts to (n, edges). A_{i,g} = i*m+g, B_{j,h} = (k+j)*m+h."""
    E = set()
    for i, j, s in darts:
        for g in range(m):
            E.add((i * m + g, (k + j) * m + (g + s) % m))
    return 2 * k * m, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.0, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: bitset-accelerated annealing over Z_m voltage lifts.
    # Target orders just above the current best, with small random offsets.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        m = max(d, base + 1 + rng.randrange(0, 3))
        darts = _anneal(m, k, d, D, rng, 6000, deadline)
        if darts is not None:
            n, e = _edges(m, k, darts)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
