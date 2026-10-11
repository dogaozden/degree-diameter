import random
import time
from math import gcd

import lib


def _groups_of_order(N):
    """All cyclic and semidirect groups Z_m x| Z_k (m*k = N, m >= 2) as (order, mul, inv)."""
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                groups.append(lib.semidirect_group(m, k, r))
    return groups


def _lift(a, d, order, mul, rng):
    """Random d-regular bipartite base on a+a vertices (union of d permutations), lifted over the group.

    Parallel darts between the same base pair get distinct voltages, so every lifted vertex has degree d.
    """
    mult = {}
    for _ in range(d):
        perm = list(range(a))
        rng.shuffle(perm)
        for i in range(a):
            mult[(i, perm[i])] = mult.get((i, perm[i]), 0) + 1
    darts = []
    for (i, j), c in mult.items():
        if c > order:
            return None
        for g in rng.sample(range(order), c):
            darts.append((i, a + j, g))
    return lib.group_lift(2 * a, darts, order, mul)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.85 * time_limit, time_limit - 5.0)
    deadline = start + max(budget, 0.5)

    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, edges = lib.araujo_lopez_graph(d - 2)
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            pass

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}, fallback
    moore = lib.moore_bound(d, D)
    group_cache = {}

    while time.monotonic() < deadline:
        a = rng.choice((1, 2, 2, 3, 3))
        best_n = best[0]
        lo = best_n // (2 * a) + 1          # need 2*a*N > best_n
        hi = moore // (2 * a)
        if lo > hi:
            continue
        N = rng.randint(lo, min(hi, lo + 15))
        if N not in group_cache:
            group_cache[N] = _groups_of_order(N)
        groups = group_cache[N]
        if not groups:
            continue
        order, mul, _ = rng.choice(groups)
        cand = _lift(a, d, order, mul, rng)
        if cand is None:
            continue
        n, edges = cand
        if n <= best_n or n > moore:
            continue
        if lib.within_diameter(n, edges, D) and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return 1, []
