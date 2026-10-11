import math
import random
import time

import lib


def _groups(M):
    """Yield (m, k, r) describing groups of order M: cyclic Z_M, then Z_m x|_r Z_k with m*k = M."""
    yield (M, 1, 0)
    for k in range(2, M + 1):
        if M % k:
            continue
        m = M // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                yield (m, k, r)


def _mul_for(M, k, m, r):
    if k == 1:
        return lib.cyclic_group(M)[1]
    return lib.semidirect_group(m, k, r)[1]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    rng = random.Random(seed)
    # Fallback: complete bipartite K_{d,d}.
    best_n, best_edges = lib.haar_graph(d, range(d))

    # Bi-Cayley search: two base vertices joined by d darts labelled with
    # group elements S, lifted over a group G of order M. This gives a
    # d-regular bipartite graph on 2M vertices. Non-cyclic groups are
    # included via semidirect products. Climb M upward and keep the
    # largest order whose lift has diameter <= D.
    TRIES = 30
    M = max(best_n // 2 + 1, d + 1)
    while time.monotonic() < deadline:
        for (m, k, r) in _groups(M):
            if time.monotonic() >= deadline:
                break
            mul = _mul_for(M, k, m, r)
            for _ in range(TRIES):
                if time.monotonic() >= deadline:
                    break
                S = rng.sample(range(M), d)
                n, edges = lib.group_lift(2, [(0, 1, g) for g in S], M, mul)
                if n > best_n and lib.within_diameter(n, edges, D):
                    best_n, best_edges = n, edges
                    break
        M += 1

    if lib.is_valid(best_n, best_edges, d, D):
        return best_n, best_edges
    return lib.haar_graph(d, range(d))
