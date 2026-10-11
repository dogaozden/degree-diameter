import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline for D = 3: incidence graph of PG(2, q) for the largest prime power q
# with q + 1 <= d. It meets the Moore bound when d - 1 is a prime power.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW HELPER: bitset evaluation of cyclic bi-Cayley lifts.
#
# A cyclic bi-Cayley graph on Z_N has vertices A_x, B_x (x in Z_N) and edges
# A_x ~ B_{x+s} for s in S, with 0 in S WLOG. A set of vertices on one side is
# stored as an N-bit integer, so "all x + s for x in X" is a bitmask rotation.
# One BFS level costs about 2d rotations on a few machine words, not a Python
# loop over vertices. This makes the diameter test roughly 20x faster than the
# set-based check, so hill-climbing can cover many more connection sets.
# ----------------------------------------------------------------------------

CLIMB_ITERS = 300   # hill-climb steps per restart


def _rot(X, t, N, mask):
    """Bitmask of {x + t mod N : x in X}."""
    return ((X << t) | (X >> (N - t))) & mask


def _cyc_cost(N, S, NS, D, mask):
    """Count (source, vertex) pairs not reached within D, from A_0 and from B_0.

    NS holds the negated shifts (-s) mod N. Translation is an automorphism, so
    eccentricities of A_0 and B_0 determine the diameter. Zero iff diameter <= D.
    """
    total = 0
    for side in (0, 1):
        RA, RB = (1, 0) if side == 0 else (0, 1)
        FA, FB = RA, RB
        for _ in range(D):
            nb = 0
            for s in S:
                nb |= _rot(FA, s, N, mask)      # B-neighbours of the A-frontier
            na = 0
            for t in NS:
                na |= _rot(FB, t, N, mask)      # A-neighbours of the B-frontier
            newB = nb & ~RB
            newA = na & ~RA
            RA |= newA
            RB |= newB
            FA, FB = newA, newB
            if not (FA or FB):
                break
        total += 2 * N - RA.bit_count() - RB.bit_count()
    return total


def _cyc_climb(N, d, D, rng, deadline, iters):
    """Hill-climb a connection set S of size d (0 in S) to zero unreached pairs.

    Sideways moves are accepted, so the walk can drift across plateaus. Random
    restarts happen until the deadline.
    """
    mask = (1 << N) - 1

    def cost(S):
        return _cyc_cost(N, S, [(-s) % N for s in S], D, mask)

    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, N), d - 1)
        cur = cost(S)
        for _ in range(iters):
            if cur == 0:
                return S
            if time.monotonic() > deadline:
                return None
            i = rng.randrange(1, d)
            c = rng.randrange(1, N)
            if c in S:
                continue
            S2 = S[:]
            S2[i] = c
            v = cost(S2)
            if v <= cur:
                S, cur = S2, v
        if cur == 0:
            return S
    return None


def _cyc_edges(N, S):
    """Edges of the bi-Cayley graph: A_x is vertex x, B_y is vertex N + y."""
    return [(x, N + (x + s) % N) for x in range(N) for s in S]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is d-regular.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best  # K_{d,d} meets the Moore bound 2d for D = 2

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: cyclic bi-Cayley lifts of order N give 2N vertices.
    # Try N just above the current best half-order, cycling through a small window.
    if d >= 3:
        slice_t = max(0.4, 0.05 * budget)
        attempt = 0
        while time.monotonic() < deadline and best[0] < moore:
            lo = best[0] // 2 + 1
            if 2 * lo > moore:
                break
            N = lo + attempt % 8
            attempt += 1
            if 2 * N > moore:
                N = lo
            if N - 1 < d - 1:
                break
            slice_end = min(deadline, time.monotonic() + slice_t)
            S = _cyc_climb(N, d, D, rng, slice_end, CLIMB_ITERS)
            if S is not None:
                consider(2 * N, _cyc_edges(N, S))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
