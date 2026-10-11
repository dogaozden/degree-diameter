import math
import random
import time

import lib


def _options(order):
    """Return all semidirect groups Z_m x| Z_k of the given order as (m, k, r) triples."""
    out = []
    for k in range(1, order + 1):
        if order % k:
            continue
        m = order // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _search(d, a, order, mul, D, rng, deadline):
    """Hill-climb voltages and layer permutations of a bipartite base with a vertices per side.

    The base is d-regular: layer i joins A-vertex j to B-vertex perms[i][j] with voltage volts[i][j].
    Returns (n, edges) with diameter <= D, or None if the deadline passes first.
    """
    perms = [rng.sample(range(a), a) for _ in range(d)]
    volts = [[rng.randrange(order) for _ in range(a)] for _ in range(d)]

    def lift():
        darts = [(j, a + perms[i][j], volts[i][j]) for i in range(d) for j in range(a)]
        return lib.group_lift(2 * a, darts, order, mul)

    n, edges = lift()
    cost = lib.bad_pairs(n, edges, D)
    while cost and time.monotonic() < deadline:
        i = rng.randrange(d)
        j = rng.randrange(a)
        old_p = perms[i][:]
        old_v = volts[i][j]
        if a > 1 and rng.random() < 0.2:
            j2 = rng.randrange(a)
            perms[i][j], perms[i][j2] = perms[i][j2], perms[i][j]
        else:
            volts[i][j] = rng.randrange(order)
        n2, e2 = lift()
        c2 = lib.bad_pairs(n2, e2, D)
        if c2 <= cost:
            cost, n, edges = c2, n2, e2
        else:
            perms[i] = old_p
            volts[i][j] = old_v
    if cost == 0:
        return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid fallback
    best_n = best[0]
    delta = 16

    while time.monotonic() < end:
        t = best_n + delta
        opts = []
        for a in (1, 2, 3, 4):
            if t % (2 * a) == 0:
                order = t // (2 * a)
                opts += [(a, order, m, k, r) for (m, k, r) in _options(order)]
        rng.shuffle(opts)

        found = None
        for a, order, m, k, r in opts[:6]:
            now = time.monotonic()
            if now >= end:
                break
            mul = lib.semidirect_group(m, k, r)[1]
            found = _search(d, a, order, mul, D, rng, min(end, now + 0.6))
            if found:
                break

        if found and lib.is_valid(found[0], found[1], d, D):
            best = found
            best_n = found[0]
            delta = min(2 * delta, 64)
        else:
            delta = max(2, delta // 2)

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return lib.haar_graph(d, range(d))
