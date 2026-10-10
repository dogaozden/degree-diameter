import random
import time

import lib


def _climb(k, m, d, D, rng, t_end):
    """Hill-climb Z_m voltages on a random bipartite base with k+k vertices and degree d.

    The base is d random perfect matchings between the A-side {0..k-1} and the B-side
    {k..2k-1}. The state is the voltages plus the matchings. Cost is lib.bad_pairs, so
    cost 0 means the lift is connected with diameter <= D. Moves that do not increase
    cost are accepted, which lets the search drift across plateaus.
    """
    perms = [rng.sample(range(k), k) for _ in range(d)]
    volt = [[rng.randrange(m) for _ in range(k)] for _ in range(d)]

    def evaluate():
        darts = [(i, k + perms[j][i], volt[j][i]) for j in range(d) for i in range(k)]
        n, edges = lib.voltage_lift(2 * k, darts, m)
        return n, edges, lib.bad_pairs(n, edges, D)

    n, edges, cost = evaluate()
    while cost > 0:
        if time.monotonic() >= t_end:
            return None
        j = rng.randrange(d)
        i = rng.randrange(k)
        if rng.random() < 0.7:
            old = volt[j][i]
            volt[j][i] = rng.randrange(m)
            undo = (0, j, i, old)
        else:
            i2 = rng.randrange(k)
            perms[j][i], perms[j][i2] = perms[j][i2], perms[j][i]
            undo = (1, j, i, i2)
        n2, e2, c2 = evaluate()
        if c2 <= cost:
            cost, n, edges = c2, n2, e2
        else:
            if undo[0] == 0:
                volt[j][i] = undo[3]
            else:
                _, j, i, i2 = undo
                perms[j][i], perms[j][i2] = perms[j][i2], perms[j][i]
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    rng = random.Random(seed)
    fallback = lib.haar_graph(d, range(d))  # K_{d,d}
    best_n, best = 2 * d, fallback
    bound = lib._moore_bound(d, D)

    # Scan base sizes k (A-side vertices per lift copy) with increasing order; for each k
    # try lift orders m from large to small, stopping at the first success for that k.
    for k in (1, 2, 3, 4, 5, 6, 8, 10, 12):
        if time.monotonic() >= deadline:
            break
        m = bound // (2 * k)
        fails = 0
        while m >= 2 and 2 * k * m > best_n and fails < 5:
            now = time.monotonic()
            if now >= deadline:
                break
            per = max(0.3, (deadline - now) / 6.0)
            t_end = min(deadline, now + per)
            res = _climb(k, m, d, D, rng, t_end)
            if res is not None:
                n, edges = res
                best_n, best = n, (n, edges)
                break
            fails += 1
            m = max(2, int(m * 0.85))

    n, edges = best
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return fallback

