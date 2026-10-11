import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: multi-orbit bi-Cayley lifts over the CYCLIC group Z_N.
#
# The parent searched single-orbit lifts over semidirect products with
# per-pair BFS on Python lists. This version instead:
#   * uses k orbits per side (2kN vertices), each layer a permutation of the
#     k A-orbits to the k B-orbits plus a shift per A-orbit, so every vertex
#     has degree d;
#   * encodes each vertex set over Z_N as an N-bit Python int, so one BFS level
#     is a few shifts and ORs per dart (rotations of bitsets);
#   * anneals layer permutations and shifts against the number of vertex pairs
#     left beyond distance D, with restarts until the deadline.
# Every candidate is checked with lib.is_valid before it replaces the best.
# ----------------------------------------------------------------------------

ANNEAL_ITERS = 3000
KS = (1, 2, 3, 4, 6)


def _best_pg(d):
    """Incidence graph of PG(2, d-1) when d-1 is a prime power (diameter 3)."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


def _rot(X, s, N, mask):
    """Bitset with bit x moved to bit (x + s) mod N."""
    s %= N
    if s == 0:
        return X
    return ((X << s) | (X >> (N - s))) & mask


def _cost(k, N, d, D, perms, shifts, mask):
    """Number of (source representative, vertex) pairs at distance > D. Zero means valid.

    Sources are A_{i,0} and B_{j,0} for every orbit; translation within each
    orbit makes these representatives sufficient.
    """
    darts = [(i, perms[L][i], shifts[L][i]) for L in range(d) for i in range(k)]
    total = 0
    sources = [(0, i) for i in range(k)] + [(1, j) for j in range(k)]
    for side, o in sources:
        RA = [0] * k
        RB = [0] * k
        FA = [0] * k
        FB = [0] * k
        if side == 0:
            RA[o] = 1
            FA[o] = 1
        else:
            RB[o] = 1
            FB[o] = 1
        for _ in range(D):
            NB = [0] * k
            NA = [0] * k
            for i, j, s in darts:
                f = FA[i]
                if f:
                    NB[j] |= _rot(f, s, N, mask)
                g = FB[j]
                if g:
                    NA[i] |= _rot(g, N - s, N, mask)
            FA = [NA[i] & ~RA[i] for i in range(k)]
            FB = [NB[j] & ~RB[j] for j in range(k)]
            for i in range(k):
                RA[i] |= FA[i]
            for j in range(k):
                RB[j] |= FB[j]
            if not any(FA) and not any(FB):
                break
        reached = sum(x.bit_count() for x in RA) + sum(x.bit_count() for x in RB)
        total += 2 * k * N - reached
    return total


def _anneal(k, N, d, D, rng, deadline, iters):
    """Anneal layer permutations and shifts; return (perms, shifts) if valid, else None."""
    mask = (1 << N) - 1
    perms = []
    shifts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        perms.append(p)
        shifts.append([rng.randrange(N) for _ in range(k)])
    cost = _cost(k, N, d, D, perms, shifts, mask)
    T0 = max(1.0, 0.05 * cost)

    for step in range(iters):
        if cost == 0:
            return perms, shifts
        if (step & 31) == 0 and time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.15
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.7:
            i = rng.randrange(k)
            old = shifts[L][i]
            new = rng.randrange(N)
            if new == old:
                continue
            shifts[L][i] = new
            c2 = _cost(k, N, d, D, perms, shifts, mask)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                shifts[L][i] = old
        else:
            a, b = rng.sample(range(k), 2)
            p = perms[L]
            p[a], p[b] = p[b], p[a]
            c2 = _cost(k, N, d, D, perms, shifts, mask)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                p[a], p[b] = p[b], p[a]

    if cost == 0:
        return perms, shifts
    return None


def _edges(k, N, d, perms, shifts):
    """Edge list of the lift: A_{i,x} ~ B_{j,x+s} for each dart (i, j, s)."""
    E = set()
    for L in range(d):
        for i in range(k):
            j = perms[L][i]
            s = shifts[L][i]
            for x in range(N):
                E.add((i * N + x, (k + j) * N + (x + s) % N))
    return 2 * k * N, sorted(E)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.7 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every d >= 1.
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

    if best[0] >= moore:
        return best

    # Main search: multi-orbit cyclic bi-Cayley lifts with annealing.
    while time.monotonic() < deadline and best[0] < moore:
        k = rng.choice(KS)
        lo = best[0] // (2 * k) + 1
        if 2 * k * lo > moore:
            k = 1
            lo = best[0] // 2 + 1
            if 2 * lo > moore:
                break
        N = lo + rng.randrange(max(1, lo // 40 + 1))
        res = _anneal(k, N, d, D, rng, deadline, ANNEAL_ITERS)
        if res is not None:
            perms, shifts = res
            n, E = _edges(k, N, d, perms, shifts)
            consider(n, E)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
