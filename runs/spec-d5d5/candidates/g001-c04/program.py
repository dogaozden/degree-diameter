import math
import random
import time

import lib


def _semidirect_candidates(N):
    """All (m, k, r) with m*k = N giving valid semidirect products Z_m x|_r Z_k (r = 1 gives cyclic)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.82 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid fallback
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])
    cap = lib._moore_bound(d, D) // 2  # bipartite: order 2N <= Moore bound

    # Bi-Cayley graphs: two base vertices A, B, and d darts (A, B, g) over a group G of order N.
    # A-vertex x joins B-vertex x*g for each g in S. Degree is exactly d, bipartite by construction.
    per_order_budget = max(0.5, 0.05 * time_limit)
    misses = 0
    N = d
    while time.monotonic() < deadline and misses < 6 and N <= cap:
        N += 1
        groups = _semidirect_candidates(N)
        if not groups:
            continue
        slice_end = min(deadline, time.monotonic() + per_order_budget)
        found = None
        while time.monotonic() < slice_end:
            m, k, r = rng.choice(groups)
            order, mul, _ = lib.semidirect_group(m, k, r)
            S = rng.sample(range(order), d)
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], order, mul)
            if len(edges) == d * order and lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found is not None:
            best = found
            misses = 0
        else:
            misses += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
