import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline: projective plane incidence graph for D = 3 (Moore-optimal when
# d - 1 is a prime power).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New helper: bitset BFS on cyclic bi-Cayley graphs.
#
# Graph on Z_N x {A, B}: A_x ~ B_{x+s} for each shift s in S (|S| = d, 0 in S).
# A set of A-vertices is a bit mask over Z_N; a shift by s is a cyclic rotation
# of that mask, so one BFS level costs |S| rotations of an N-bit integer.
# Translations are automorphisms, so eccentricities of A_0 and B_0 determine the
# diameter. The cost is the number of (source, target) pairs at distance > D.
# ----------------------------------------------------------------------------

def _unreached(N, S, D):
    """Number of (source, vertex) pairs with source in {A_0, B_0} not within distance D."""
    full = (1 << N) - 1
    neg = [(N - s) % N for s in S]  # shifts for B -> A steps
    total = 0
    for side in (0, 1):  # 0: source A_0, 1: source B_0
        seenA = 1 if side == 0 else 0
        seenB = 1 if side == 1 else 0
        front = 1
        on_A = (side == 0)
        for _ in range(D):
            if not front:
                break
            nxt = 0
            if on_A:
                for s in S:
                    nxt |= ((front << s) | (front >> (N - s))) & full
                nxt &= ~seenB
                seenB |= nxt
            else:
                for s in neg:
                    nxt |= ((front << s) | (front >> (N - s))) & full
                nxt &= ~seenA
                seenA |= nxt
            front = nxt
            on_A = not on_A
        total += 2 * N - seenA.bit_count() - seenB.bit_count()
    return total


def _anneal_cyclic(N, d, D, rng, deadline, iters):
    """Simulated annealing over connection sets S (0 fixed in S) to zero unreached pairs.

    Returns S when the cyclic bi-Cayley graph has diameter <= D, else None.
    """
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, S, D)
    T0, T1 = 2.0, 0.3
    for it in range(iters):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = list(S)
        S2[i] = c
        v = _unreached(N, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S, cur = S2, v
    return S if cur == 0 else None


def _cyclic_graph(N, S):
    """Edges of the cyclic bi-Cayley graph: A_x = x, B_y = N + y, A_x ~ B_{x+s}."""
    return 2 * N, [(x, N + (x + s) % N) for x in range(N) for s in S]


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
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and meets the Moore bound 2d for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

    # Search over cyclic bi-Cayley graphs of order 2N. N moves up after a success
    # and down after a failure, so the walk hovers around the feasibility boundary.
    N = max(d, min(moore // 2, int(0.4 * moore / 2)))
    slice_len = max(0.4, 0.03 * budget)
    iters = 12000
    max_N = moore // 2

    while time.monotonic() < deadline and d <= N <= max_N:
        if best[0] >= moore:
            break
        slice_end = min(deadline, time.monotonic() + slice_len)
        S = _anneal_cyclic(N, d, D, rng, slice_end, iters)
        if S is not None:
            n2, e2 = _cyclic_graph(N, S)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
            N += 1
        else:
            N -= 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
