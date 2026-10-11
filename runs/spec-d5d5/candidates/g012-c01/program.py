import math
import random
import time

import lib


_GROUP_CACHE = {}
ANNEAL_ITERS = 1200


def _group_tables(m, k, r):
    """Cached (order, tab) for Z_m x|_r Z_k, where tab[s][g] = g * s."""
    key = (m, k, r)
    hit = _GROUP_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, _ = lib.semidirect_group(m, k, r)
    tab = [[mul(g, s) for g in range(order)] for s in range(order)]
    val = (order, tab)
    if len(_GROUP_CACHE) > 64:
        _GROUP_CACHE.clear()
    _GROUP_CACHE[key] = val
    return val


def _groups_of_order(G):
    """All semidirect parameters (m, k, r) with m * k = G and the required r^k = 1 mod m."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _lift_edges(k, G, tab, darts):
    """Edge set of the bi-Cayley-type lift: dart (i, j, s) joins A_{i,g} to B_{j, g*s}."""
    E = set()
    for i, j, s in darts:
        row = tab[s]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + row[g]))
    return E


def _miss(N, E, D):
    """Number of ordered vertex pairs at distance > D (bit-parallel ball growth)."""
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    R = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = R[v]
            for u in adj[v]:
                x |= R[u]
            new.append(x)
        R = new
    return sum(N - x.bit_count() for x in R)


def _cost(k, G, tab, darts, D):
    """Unreached pairs plus a heavy penalty for duplicate edges (duplicates lower degree)."""
    N = 2 * k * G
    E = _lift_edges(k, G, tab, darts)
    dup = len(darts) * G - len(E)
    if dup:
        return dup * N + _miss(N, E, D)
    return _miss(N, E, D)


def _anneal(d, D, k, G, tab, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments.

    Layer L holds k darts (i, p_L(i), s); p_L is a permutation, so every vertex
    has degree exactly d before duplicate removal.
    """
    N = 2 * k * G
    darts = []
    for _L in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])

    cost = _cost(k, G, tab, darts, D)
    T0 = max(3.0, 0.01 * cost)
    T_end = 0.2

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T_end / T0) ** (it / max(1, iters))

        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, tab, darts, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, tab, darts, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        E = _lift_edges(k, G, tab, darts)
        return N, sorted(E)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed * 1000003 + d * 101 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallbacks: K_{d,d} has diameter 2; C_{2D} has diameter D for d = 2.
    best = lib.haar_graph(d, range(d))
    if d == 2:
        best = (2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        best = (best[0], [(min(u, v), max(u, v)) for u, v in best[1]])
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    if D == 2 or d <= 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact structured record for D = 3 when d - 1 is a prime power (e.g. Heawood for d = 3).
    if D == 3 and lib.is_prime_power(d - 1):
        n_pg, e_pg = lib.projective_plane_incidence(d - 1)
        consider(n_pg, e_pg)

    # Main search: multi-base voltage lifts over semidirect products, annealed.
    ks = (1, 2, 2, 3, 3, 4)
    while time.monotonic() < deadline and best[0] < moore:
        target = best[0] + 2
        if target > moore:
            break
        k = rng.choice(ks)
        G_min = -(-target // (2 * k))
        if 2 * k * G_min > moore:
            continue
        G = G_min + rng.randrange(3)
        groups = _groups_of_order(G)
        if not groups:
            continue
        m, k2, r = rng.choice(groups)
        order, tab = _group_tables(m, k2, r)
        res = _anneal(d, D, k, order, tab, rng, deadline, ANNEAL_ITERS)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
