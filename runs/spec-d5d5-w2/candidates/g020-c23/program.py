import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Family: bi-Cayley graphs over the cyclic group Z_N.
#   A_x ~ B_{x+s} for s in S, |S| = d, so the graph is bipartite and d-regular.
# Distances are translation invariant, so it suffices to check balls around
# A_0 and B_0. Balls are stored as N-bit integers and expanded by cyclic
# rotations, which makes each cost evaluation cheap enough for annealing.
# ----------------------------------------------------------------------------

def _rot(X, s, N, mask):
    """Bitmask with bit (x + s) mod N set for every bit x set in X."""
    if s == 0:
        return X
    return ((X << s) | (X >> (N - s))) & mask


def _cost(N, S, Sm, mask, D):
    """Number of (source, vertex) pairs at distance > D, over sources A_0 and B_0.

    Sm holds the negated shifts (-s) mod N. Zero means the graph has diameter <= D.
    """
    full = 2 * N
    total = 0
    for a0, b0 in ((1, 0), (0, 1)):
        ball_a, ball_b = a0, b0
        for _ in range(D):
            n_a, n_b = ball_a, ball_b
            for s in S:
                n_b |= _rot(ball_a, s, N, mask)   # A_x -> B_{x+s}
            for s in Sm:
                n_a |= _rot(ball_b, s, N, mask)   # B_y -> A_{y-s}
            ball_a, ball_b = n_a, n_b
            if ball_a == mask and ball_b == mask:
                break
        total += full - ball_a.bit_count() - ball_b.bit_count()
    return total


def _search(N, d, D, rng, deadline):
    """Simulated annealing over S (containing 0, WLOG) to reach zero cost. Returns S or None."""
    mask = (1 << N) - 1
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, N), d - 1)
        cur = _cost(N, S, [(-s) % N for s in S], mask, D)
        T = 2.0
        for _ in range(6000):
            if cur == 0:
                return S
            if time.monotonic() >= deadline:
                return None
            i = rng.randrange(1, d)
            c = rng.randrange(1, N)
            if c in S:
                continue
            S2 = S[:]
            S2[i] = c
            v = _cost(N, S2, [(-x) % N for x in S2], mask, D)
            if v <= cur or rng.random() < math.exp((cur - v) / T):
                S, cur = S2, v
            T = max(0.15, T * 0.999)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and order 2d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)
    rng = random.Random(seed)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Calibration-friendly structured start for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))

    # Main search: abelian bi-Cayley lifts over Z_N, sweeping N upward.
    N = max(d, best[0] // 2 + 1)
    hi = moore // 2
    slice_t = max(1.0, budget / 30.0)
    while N <= hi and time.monotonic() < deadline:
        if 2 * N > best[0]:
            S = _search(N, d, D, rng, min(deadline, time.monotonic() + slice_t))
            if S is not None:
                edges = [(x, N + (x + s) % N) for x in range(N) for s in S]
                consider(2 * N, edges)
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
