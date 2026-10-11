import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New helper: bitset BFS for cyclic bi-Cayley (Haar) graphs.
#
# The Haar graph of Z_N with connection set S joins A_x to B_{x+s} for s in S.
# Translation by Z_N is an automorphism, so the distance profile from A_0 and
# from B_0 determines the whole graph. Each BFS layer is kept as an N-bit
# integer, with bit x set when vertex x is in the layer. A cyclic rotation of
# that integer by s moves every vertex x to x+s at once. One BFS layer
# therefore costs about 2d big-integer shifts, instead of a Python loop over
# all vertices. This makes the annealing cost function roughly an order of
# magnitude cheaper than a plain BFS.
# ----------------------------------------------------------------------------

def _rot(X, s, N, FULL):
    """Cyclically rotate the N-bit mask X so that bit x moves to bit (x + s) mod N."""
    if s == 0:
        return X
    return ((X << s) | (X >> (N - s))) & FULL


def _cyc_unreached(N, S, D, FULL):
    """Number of ordered (source, target) pairs at distance > D, for sources A_0 and B_0.

    A_x ~ B_{x+s} for s in S. From A_0 we get all distances to A and to B; from B_0
    we get all distances from B. Together these give every pair that matters, by
    translation invariance.
    """
    negS = [(N - s) % N for s in S]
    total = 0
    for side in (0, 1):
        seenA = 1 if side == 0 else 0
        seenB = 1 if side == 1 else 0
        fA, fB = seenA, seenB
        for _ in range(D):
            if not fA and not fB:
                break
            nB = 0
            for s in S:
                nB |= _rot(fA, s, N, FULL)
            nB &= ~seenB & FULL
            nA = 0
            for t in negS:
                nA |= _rot(fB, t, N, FULL)
            nA &= ~seenA & FULL
            seenA |= nA
            seenB |= nB
            fA, fB = nA, nB
        total += 2 * N - seenA.bit_count() - seenB.bit_count()
    return total


def _search_cyc(N, d, D, rng, deadline, iters):
    """Annealing over connection sets S (containing 0 WLOG) of size d in Z_N.

    Restarts until a set with zero unreached pairs is found or the deadline passes.
    """
    if d < 2 or N < d:
        return None
    FULL = (1 << N) - 1
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, N), d - 1)
        cur = _cyc_unreached(N, S, D, FULL)
        T0 = 3.0
        for step in range(iters):
            if cur == 0:
                break
            if (step & 255) == 0 and time.monotonic() > deadline:
                break
            temp = T0 * (1.0 - step / iters) + 0.1
            i = rng.randrange(1, d)
            c = rng.randrange(1, N)
            if c in S:
                continue
            S2 = S[:]
            S2[i] = c
            v = _cyc_unreached(N, S2, D, FULL)
            delta = v - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                S, cur = S2, v
        if cur == 0:
            return S
    return None


# ----------------------------------------------------------------------------
# D = 3 baseline: incidence graph of PG(2, q), q + 1 <= d (Moore-optimal when d-1 is a prime power).
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


ITERS = 3000  # annealing steps per restart


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and order 2d; it is the safe fallback.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

    # Main search: cyclic Haar graphs of growing order N (lift has 2N vertices).
    while time.monotonic() < deadline and best[0] < moore:
        lo = max(d, best[0] // 2 + 1)
        if 2 * lo > moore:
            break
        W = max(2, lo // 30)
        N = lo + rng.randrange(W)
        if 2 * N > moore:
            N = lo
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        chunk = min(remaining, max(1.5, remaining / 4.0))
        S = _search_cyc(N, d, D, rng, time.monotonic() + chunk, ITERS)
        if S is not None:
            n2, e2 = lib.haar_graph(N, S)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
