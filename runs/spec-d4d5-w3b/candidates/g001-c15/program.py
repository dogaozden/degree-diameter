import math
import random
import time

import lib


# Idea (new in this version): bad-pair-guided voltage hill-climbing on
# bi-Cayley lifts over semidirect products Z_m x|_r Z_k.
#
# The base graph is bipartite with s vertices per side (s = 1 or 2), and every
# base vertex has degree d. Each base dart (a, b) carries a group element g, and
# the lift joins (a, x) to (b, x*g). Because the base is bipartite, the lift is
# bipartite, and the degree is exactly d. The search does not just test
# diameter as a yes/no question. It minimises lib.bad_pairs (the number of
# vertex pairs at distance > D) by changing one voltage at a time, and it accepts
# sideways moves. Each group order is tried in ascending order, so the result
# is the largest order that succeeds.


def _haar_search(d, D, rng, deadline):
    """Parent-style Haar graph search, used as a quick baseline."""
    best = lib.haar_graph(d, range(d))
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def _groups_of_order(order):
    """All (m, k, r) with m*k = order describing Z_m x|_r Z_k (cyclic when k = 1)."""
    out = [(order, 1, 1)]
    for k in range(2, order + 1):
        if order % k:
            continue
        m = order // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _base_pairs(s, d, x):
    """Bipartite base multigraph with s vertices per side, all degrees d.

    Side A = {0..s-1}, side B = {s..2s-1}. Each pair (a, b) is one dart slot.
    """
    if s == 1:
        return [(0, 1)] * d
    # s == 2: A = {0, 1}, B = {2, 3}, multiplicity matrix [[x, d-x], [d-x, x]].
    return ([(0, 2)] * x + [(0, 3)] * (d - x)
            + [(1, 2)] * (d - x) + [(1, 3)] * x)


def _lift(s, order, mul, darts):
    return lib.group_lift(2 * s, darts, order, mul)


def _climb(d, D, s, x, order, mul, rng, deadline, max_steps):
    """Hill-climb voltages to make the lift have diameter <= D. Returns (n, edges) or None."""
    if order < d:
        return None
    pairs = _base_pairs(s, d, x)
    steps = 0
    while time.monotonic() < deadline and steps < max_steps:
        # Random start with distinct voltages inside each base pair.
        darts, used = [], set()
        for a, b in pairs:
            while True:
                g = rng.randrange(order)
                if (a, b, g) not in used:
                    break
            used.add((a, b, g))
            darts.append([a, b, g])
        cur_n, cur_edges = _lift(s, order, mul, darts)
        cur = lib.bad_pairs(cur_n, cur_edges, D)
        stall = 0
        while (cur > 0 and stall < 400 and steps < max_steps
               and time.monotonic() < deadline):
            steps += 1
            i = rng.randrange(len(darts))
            a, b, g_old = darts[i]
            g = rng.randrange(order)
            if g == g_old or any(dd[0] == a and dd[1] == b and dd[2] == g
                                 for dd in darts):
                continue
            darts[i][2] = g
            n, edges = _lift(s, order, mul, darts)
            new = lib.bad_pairs(n, edges, D)
            if new <= cur:
                stall = 0 if new < cur else stall + 1
                cur, cur_n, cur_edges = new, n, edges
            else:
                darts[i][2] = g_old
                stall += 1
        if cur == 0:
            return cur_n, cur_edges
    return None


def _attempt(n_target, d, D, rng, deadline):
    """Try to find a valid lift with exactly n_target vertices before the deadline."""
    cands = []
    for s in (1, 2):
        if n_target % (2 * s):
            continue
        order = n_target // (2 * s)
        if order < d:
            continue
        xs = range(d + 1) if s == 2 else [0]
        for m, k, r in _groups_of_order(order):
            for x in xs:
                cands.append((s, order, m, k, r, x))
    rng.shuffle(cands)
    for s, order, m, k, r, x in cands:
        if time.monotonic() >= deadline:
            break
        _, mul, _ = lib.semidirect_group(m, k, r)
        cand_deadline = min(deadline, time.monotonic() + 2.0)
        res = _climb(d, D, s, x, order, mul, rng, cand_deadline, 3000)
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            return res
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, 0.8 * time_limit - 1.0)
    deadline = start + budget

    # Projective plane is optimal for D = 3 when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
    try:
        h = _haar_search(d, D, rng, start + 0.15 * budget)
        if h[0] > best[0] and lib.is_valid(h[0], h[1], d, D):
            best = h

        moore = lib.moore_bound(d, D)
        # Ascending ladder of target orders: each success raises the bar.
        t = best[0] + 2
        while time.monotonic() < deadline - 0.2 and t <= moore:
            remaining = deadline - time.monotonic()
            slice_t = min(remaining, max(0.8, 0.08 * remaining))
            res = _attempt(t, d, D, rng, time.monotonic() + slice_t)
            if res is not None and res[0] > best[0]:
                best = res
                t = res[0] + 2
            else:
                t += 2
    except Exception:
        pass

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return lib.haar_graph(d, range(d))
