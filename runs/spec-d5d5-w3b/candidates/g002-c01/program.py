import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Family: cyclic voltage lifts with k A-base and k B-base vertices.
#
# Base graph: d perfect matchings (layers) between the A-base and B-base
# vertices. Layer L pairs A-base i with B-base pis[L][i], and carries a
# voltage volt[L][i] in Z_m. The lift has vertices A_{i,g} and B_{j,h}, and
# the edge A_{i,g} -- B_{pis[L][i], g + volt[L][i]} for every layer L.
#
# Each vertex gets at most one edge per layer, so the degree is at most d.
# Duplicate edges only lower the degree, so they stay valid.
#
# Search: simulated annealing over voltages and layer matchings. The cost is
# the number of ordered vertex pairs not reached within distance D, computed
# with bit-parallel reachability (one big-int bitmask per vertex). This is
# much cheaper per step than the per-source BFS used before, so the annealer
# gets many more moves.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost(k, m, d, D, pis, volt):
    """Ordered vertex pairs not within distance D in the lift. Zero means diameter <= D."""
    N = 2 * k * m
    base = k * m
    adj = [[] for _ in range(N)]
    for L in range(d):
        p = pis[L]
        s = volt[L]
        for i in range(k):
            boff = base + p[i] * m
            sh = s[i]
            for g in range(m):
                a = i * m + g
                b = boff + (g + sh) % m
                adj[a].append(b)
                adj[b].append(a)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        changed = False
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
            if r != reach[v]:
                changed = True
        reach = new
        if not changed:
            break
    return sum(N - r.bit_count() for r in reach)


def _edges(k, m, d, pis, volt):
    """Edge list of the lift; A-vertices are 0..k*m-1, B-vertices follow."""
    base = k * m
    E = set()
    for L in range(d):
        for i in range(k):
            j = pis[L][i]
            sh = volt[L][i]
            for g in range(m):
                E.add((i * m + g, base + j * m + (g + sh) % m))
    return 2 * base, sorted(E)


def _anneal(k, m, d, D, rng, deadline):
    """Anneal voltages and layer matchings until the lift has diameter <= D, or time runs out."""
    pis = [rng.sample(range(k), k) for _ in range(d)]
    volt = [[rng.randrange(m) for _ in range(k)] for _ in range(d)]
    cost = _cost(k, m, d, D, pis, volt)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0 = max(2.0, 0.05 * cost)
    T1 = 0.3

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - t0) / span)
        temp = T0 * (T1 / T0) ** frac

        if k < 2 or rng.random() < 0.6:
            L = rng.randrange(d)
            i = rng.randrange(k)
            old = volt[L][i]
            new = rng.randrange(m)
            if new == old:
                continue
            volt[L][i] = new
            c2 = _cost(k, m, d, D, pis, volt)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                volt[L][i] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            p = pis[L]
            p[a], p[b] = p[b], p[a]
            c2 = _cost(k, m, d, D, pis, volt)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                p[a], p[b] = p[b], p[a]

    if cost == 0:
        return _edges(k, m, d, pis, volt)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, bipartite with diameter 2 (valid for every D >= 2).
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: cyclic multi-base voltage lifts, aiming above the current best.
    slice_len = max(3.0, 0.12 * budget)
    while best[0] < moore and time.monotonic() < deadline - 0.2:
        n_best = best[0]
        km_min = n_best // 2 + 1          # need 2*k*m > n_best
        if 2 * km_min > moore:
            break

        k = rng.choice([1, 2, 2, 3, 3, 4, 5, 6])
        m = -(-km_min // k)                # ceil(km_min / k)
        if rng.random() < 0.35:
            m += rng.randrange(1, 3)
        m = max(2, m)
        if 2 * k * m > moore:
            k = 1
            m = max(2, km_min)
            if 2 * k * m > moore:
                break

        slice_end = min(deadline, time.monotonic() + slice_len)
        res = _anneal(k, m, d, D, rng, slice_end)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
