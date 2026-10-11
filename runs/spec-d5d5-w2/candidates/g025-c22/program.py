import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bitset multi-base cyclic lifts.
#
# A lift has k base vertices per side. Vertex (A, i, x) and (B, j, y) live over
# Z_N, and each dart (i, j, s) joins (A, i, x) to (B, j, x+s). Each layer L
# contributes one dart per A-base vertex, so the degree is exactly d. Translation
# by Z_N is an automorphism, so the source set {A_i,0, B_j,0} suffices for the
# diameter check. Reachability is computed with Python big-int bitsets, where
# a shift by s is a cyclic rotation of an N-bit mask.
# ----------------------------------------------------------------------------

BIG = 10 ** 6
SLICE = 4.0          # seconds per annealing run
ANNEAL_ITERS = 40000


def _rot(X, s, N, full):
    """Rotate an N-bit mask: bit x moves to (x + s) mod N."""
    if s == 0:
        return X
    return ((X << s) | (X >> (N - s))) & full


def _reach_cost(k, N, darts, D, full):
    """Total number of (source, vertex) pairs at distance > D, over all 2k sources."""
    total = 0
    nodes = 2 * k * N
    sources = [(0, i) for i in range(k)] + [(1, j) for j in range(k)]
    for side, i0 in sources:
        seenA = [0] * k
        seenB = [0] * k
        fA = [0] * k
        fB = [0] * k
        if side == 0:
            seenA[i0] = 1
            fA[i0] = 1
        else:
            seenB[i0] = 1
            fB[i0] = 1
        for _ in range(D):
            nB = [0] * k
            nA = [0] * k
            for i, j, s in darts:
                f = fA[i]
                if f:
                    nB[j] |= _rot(f, s, N, full)
                g = fB[j]
                if g:
                    nA[i] |= _rot(g, (N - s) % N, N, full)
            any_new = False
            for j in range(k):
                x = nB[j] & ~seenB[j]
                nB[j] = x
                if x:
                    seenB[j] |= x
                    any_new = True
            for i in range(k):
                x = nA[i] & ~seenA[i]
                nA[i] = x
                if x:
                    seenA[i] |= x
                    any_new = True
            fA, fB = nA, nB
            if not any_new:
                break
        reached = sum(b.bit_count() for b in seenA) + sum(b.bit_count() for b in seenB)
        total += nodes - reached
    return total


def _cost(k, N, darts, D, full):
    """Cost of a dart configuration; duplicate darts are heavily penalised."""
    if len(set(darts)) < len(darts):
        return BIG
    return _reach_cost(k, N, darts, D, full)


def _random_darts(k, N, d, rng):
    """One random permutation per layer, with a random shift for each dart."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append((i, p[i], rng.randrange(N)))
    return darts


def _anneal(d, D, k, N, rng, deadline, iters):
    """Simulated annealing over shifts and per-layer B-assignments. Returns darts or None."""
    full = (1 << N) - 1
    darts = None
    for _ in range(50):
        cand = _random_darts(k, N, d, rng)
        if len(set(cand)) == len(cand):
            darts = cand
            break
    if darts is None:
        return None

    cost = _cost(k, N, darts, D, full)
    T0 = max(1.0, 0.05 * cost) if cost < BIG else 1.0
    T_end = 0.3
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.6 or k == 1:
            idx = rng.randrange(len(darts))
            i, j, s = darts[idx]
            ns = rng.randrange(N)
            if ns == s:
                continue
            darts[idx] = (i, j, ns)
            c2 = _cost(k, N, darts, D, full)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx] = (i, j, s)
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            ja = darts[ia][1]
            jb = darts[ib][1]
            if ja == jb:
                continue
            old_a, old_b = darts[ia], darts[ib]
            darts[ia] = (a, jb, old_a[2])
            darts[ib] = (b, ja, old_b[2])
            c2 = _cost(k, N, darts, D, full)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia] = old_a
                darts[ib] = old_b

    if cost == 0:
        return darts
    return None


def _lift_edges(k, N, darts):
    """Expand darts into the simple bipartite graph on 2kN vertices."""
    E = set()
    for i, j, s in darts:
        for x in range(N):
            E.add((i * N + x, (k + j) * N + (x + s) % N))
    return 2 * k * N, sorted(E)


# ----------------------------------------------------------------------------
# Projective plane baseline for D = 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if best[0] < n <= moore and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: multi-base cyclic bitset lifts with annealing, aimed above the best order.
    ks = [1, 2, 3, 4]
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        cands = [k for k in ks if 2 * k * (n_best // (2 * k) + 1) <= moore]
        if not cands:
            break
        k = rng.choice(cands)
        lo = n_best // (2 * k) + 1
        hi_allowed = moore // (2 * k)
        if lo > hi_allowed:
            continue
        window = max(2, lo // 15)
        N = rng.randint(lo, min(hi_allowed, lo + window))
        if N < 2:
            continue
        slice_end = min(deadline, time.monotonic() + SLICE)
        darts = _anneal(d, D, k, N, rng, slice_end, ANNEAL_ITERS)
        if darts is not None:
            n, e = _lift_edges(k, N, darts)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
