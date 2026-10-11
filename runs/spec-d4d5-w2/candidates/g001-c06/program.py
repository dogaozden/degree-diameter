import math
import random
import time

import lib


def _groups(N):
    """Return multiplication functions for cyclic Z_N and every semidirect Z_m x| Z_k with m*k = N (k >= 2)."""
    muls = [lib.cyclic_group(N)[1]]
    if N > 5000:  # keep enumeration cheap for large orders
        return muls
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
                continue
            _, mul, _ = lib.semidirect_group(m, k, r)
            muls.append(mul)
    return muls


def _try_order(N, d, D, rng, t_end):
    """Random search over Haar-type lifts of order N: two base vertices joined by d darts with group voltages.

    Vertex A_x is adjacent to B_{x*s} for s in S, so the lift is bipartite with degree d.
    Returns (n, edges) for the first connection set whose lift has diameter <= D, else None.
    """
    muls = _groups(N)
    while time.monotonic() < t_end:
        mul = muls[rng.randrange(len(muls))]
        S = rng.sample(range(N), d)
        darts = [(0, 1, s) for s in S]
        n, edges = lib.group_lift(2, darts, N, mul)
        if len(edges) == N * d and lib.within_diameter(n, edges, D):
            return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    t_end = start + 0.75 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    rng = random.Random(seed)

    lo = d
    hi = max(lo, min(lib.moore_bound(d, D) // 2, 4000))

    # Sweep group orders downward from the largest allowed; the first success is the largest found.
    # Each order gets an equal share of the remaining time, so no single order starves the rest.
    N = hi
    while N >= lo:
        now = time.monotonic()
        if now >= t_end:
            break
        remaining = N - lo + 1
        slice_end = now + (t_end - now) / remaining
        res = _try_order(N, d, D, rng, slice_end)
        if res is not None:
            n, edges = res
            if lib.is_valid(n, edges, d, D):
                return n, edges
        N -= 1

    return fallback
