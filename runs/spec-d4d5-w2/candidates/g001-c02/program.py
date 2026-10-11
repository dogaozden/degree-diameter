import math
import random
import time

import lib


def _groups(N):
    """All semidirect products Z_m x|_r Z_k with m*k = N, as (order, mul) pairs."""
    out = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        for r in range(m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
                continue
            order, mul, _ = lib.semidirect_group(m, k, r)
            out.append((order, mul))
    return out


def _search(N, d, D, rng, trials, deadline):
    """Random bi-Cayley graphs over every group of order N: parts A and B are both the group,
    a_x is joined to b_{x*g} for g in a random d-subset S. Returns (n, edges) or None."""
    groups = _groups(N)
    if not groups:
        return None
    for _ in range(trials):
        if time.monotonic() >= deadline:
            break
        order, mul = groups[rng.randrange(len(groups))]
        if order < d:
            continue
        S = rng.sample(range(order), d)
        n, edges = lib.group_lift(2, [(0, 1, g) for g in S], order, mul)
        if lib.within_diameter(n, edges, D):
            return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    rng = random.Random(seed)
    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    best = fallback
    best_N = d
    upper = lib.moore_bound(d, D) // 2

    trials = 400
    while time.monotonic() < deadline and best_N < upper:
        improved = False
        for N in range(best_N + 1, upper + 1):
            if time.monotonic() >= deadline:
                break
            res = _search(N, d, D, rng, trials, deadline)
            if res is not None:
                best, best_N = res, N
                improved = True
        if not improved:
            trials *= 2  # widen the search when a full pass finds nothing new

    n, edges = best
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return fallback
