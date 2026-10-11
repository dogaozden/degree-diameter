import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Constructions:
#   * D = 1, 2 and d <= 2: trivial graphs (K2, K_{d,d}, even cycles).
#   * D = 3: incidence graph of PG(2, q) when available.
#   * D >= 3 (general): multi-base voltage lifts over semidirect products
#     Z_m x|_r Z_k with k base vertices per side. Each base vertex has d darts
#     (one per layer), so the lift is d-regular. Voltages and target
#     assignments are found by simulated annealing that minimises the number
#     of vertex pairs farther apart than D.
# Every candidate is checked with lib.is_valid before it is accepted, and a
# valid fallback (K_{d,d}, diameter 2) is kept throughout.
# ----------------------------------------------------------------------------

_BIG = 10 ** 6
ANNEAL_ITERS = 1500
T_START = 2.0
T_END = 0.2
_TABLE_CACHE = {}


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _semidirect_params(G):
    """All (m, k, r) with m * k = G giving a valid semidirect product Z_m x|_r Z_k."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _group_table(m, k, r):
    """Return (order, T) with T[g][s] = g * s in Z_m x|_r Z_k (cached)."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, _ = lib.semidirect_group(m, k, r)
    T = [[mul(g, s) for s in range(order)] for g in range(order)]
    if len(_TABLE_CACHE) > 32:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = (order, T)
    return order, T


def _adjacency(k, G, T, darts):
    """Adjacency lists of the lift; None if two darts coincide (duplicate edges)."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    seen = set()
    for i, j, s in darts:
        key = (i, j, s)
        if key in seen:
            return None
        seen.add(key)
        a0 = i * G
        b0 = (k + j) * G
        for g in range(G):
            a = a0 + g
            b = b0 + T[g][s]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _unreached(k, G, adj, D):
    """Pairs (representative, vertex) not within distance D.

    Left translations are automorphisms, so one representative per layer
    (A_i at identity, B_j at identity) suffices.
    """
    N = 2 * k * G
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _cost(k, G, T, darts, D):
    adj = _adjacency(k, G, T, darts)
    if adj is None:
        return _BIG
    return _unreached(k, G, adj, D)


def _anneal(d, D, k, G, T, rng, deadline, iters):
    """Anneal darts (i, j, s): layer L has darts (i, p_L(i), s) for a permutation p_L.

    Returns the dart list if a valid lift (zero unreached pairs) is found, else None.
    """
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, T, darts, D)
    ratio = T_END / T_START

    for step in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = T_START * (ratio ** (step / max(1, iters)))

        if k == 1 or rng.random() < 0.8:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, T, darts, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, T, darts, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return darts
    return None


def _edges(k, G, T, darts):
    E = set()
    for i, j, s in darts:
        for g in range(G):
            E.add((i * G + g, (k + j) * G + T[g][s]))
    return sorted(E)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    ks = (2, 3, 4)
    while best_n < moore and time.monotonic() < deadline:
        # Target orders just above the current best: n = 2 * k * G.
        feasible = [k for k in ks if 2 * k * (best_n // (2 * k) + 1) <= moore]
        if not feasible:
            break
        k = rng.choice(feasible)
        lo = best_n // (2 * k) + 1
        G = lo + rng.randrange(max(1, lo // 25) + 1)
        if 2 * k * G > moore:
            G = lo
        if G < 2:
            continue
        groups = _semidirect_params(G)
        if not groups:
            continue
        m, k2, r = rng.choice(groups)
        order, T = _group_table(m, k2, r)
        darts = _anneal(d, D, k, order, T, rng, deadline, ANNEAL_ITERS)
        if darts is not None:
            consider(2 * k * order, _edges(k, order, T, darts))

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
