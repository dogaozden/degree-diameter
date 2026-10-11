import math
import random
import time

import lib

_group_cache = {}


def _groups_of_order(o):
    """Return all (m, k, r) with m*k = o for which Z_m x|_r Z_k is defined (r^k = 1 mod m, gcd(r, m) = 1)."""
    if o in _group_cache:
        return _group_cache[o]
    out = []
    for k in range(1, o + 1):
        if o % k:
            continue
        m = o // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    _group_cache[o] = out
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit

    # D = 3 with d - 1 a prime power: the projective plane incidence graph meets the Moore bound.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Always-valid fallback: K_{d,d} has diameter 2 <= D (for D >= 2).
    best_n, best_edges = lib.haar_graph(d, range(d))
    if d < 2 or D < 2:
        return best_n, best_edges
    best_order = d  # the order of the group behind K_{d,d} (the cyclic group Z_d)

    # Vertex count of the lift is 2 * order, so order <= moore_bound / 2.
    cap = min(lib.moore_bound(d, D) // 2, 400)

    rng = random.Random(seed)
    while time.monotonic() < deadline and best_order < cap:
        # Aim just above the current best order; occasionally explore a wider window.
        span = min(6, cap - best_order)
        o = best_order + 1 + rng.randrange(span)
        groups = _groups_of_order(o)
        if not groups:
            continue
        m, k, r = rng.choice(groups)
        order, mul, _ = lib.semidirect_group(m, k, r)
        if order < d:
            continue
        # Bipartite base graph with two vertices and d darts, all with distinct voltages,
        # so every vertex of the lift has degree exactly d.
        S = rng.sample(range(order), d)
        n, edges = lib.group_lift(2, [(0, 1, g) for g in S], order, mul)
        if n > best_n and lib.is_valid(n, edges, d, D):
            best_n, best_edges = n, edges
            best_order = o

    return best_n, best_edges
