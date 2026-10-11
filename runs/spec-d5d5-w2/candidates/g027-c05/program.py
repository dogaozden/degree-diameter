import math
import random
import time

import lib

BIG = 10 ** 9
_TABLE_CACHE = {}


def _groups(G):
    """Semidirect parameters (m, k, r) with m * k = G, giving Z_m x|_r Z_k (k = 1 gives cyclic)."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(m, k, r):
    """Cached (order, T) where T[x][g] = x * g for the semidirect product Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, _ = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    if len(_TABLE_CACHE) >= 64:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = (order, T)
    return order, T


def _cost(k, G, D, darts, T):
    """Unreached (representative, vertex) pairs for a k-base lift over a group of order G.

    Dart (i, j, g) joins A_{i,x} to B_{j, x*g} for every x. Left translation is an
    automorphism, so one representative per base vertex on each side suffices.
    Zero means the lift has diameter <= D. Duplicate darts give BIG.
    """
    seen = set()
    for dt in darts:
        key = (dt[0], dt[1], dt[2])
        if key in seen:
            return BIG
        seen.add(key)
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, g in darts:
        ba = i * G
        bb = (k + j) * G
        for x in range(G):
            a = ba + x
            b = bb + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    for src in reps:
        seen_v = bytearray(N)
        seen_v[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen_v[v]:
                        seen_v[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _edges(k, G, T, darts):
    E = set()
    for i, j, g in darts:
        for x in range(G):
            E.add((i * G + x, (k + j) * G + T[x][g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, T, rng, deadline):
    """Simulated annealing over voltages and per-layer base permutations.

    Layer L is a permutation p_L of the k base vertices, so every vertex has degree d.
    Temperature follows a geometric schedule in elapsed time. Returns (n, edges) or None.
    """
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, D, darts, T)
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    T0, T1 = 2.0, 0.05

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - t_start) / span)
        temp = T0 * (T1 / T0) ** frac

        if rng.random() < 0.6 or k == 1:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, T)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, T)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, T, darts)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is always valid.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)
    best_n = best[0]

    # Projective plane incidence graph meets the Moore bound for D = 3 when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Multi-base lifts over semidirect products, annealed. Each attempt targets
    # an order just above the current best.
    ks = [1, 2, 3]
    per_try = max(1.0, 0.1 * budget)
    while best_n < moore and time.monotonic() < deadline:
        k = rng.choice(ks)
        lo = best_n // (2 * k) + 1
        if 2 * k * lo > moore:
            ks = [kk for kk in ks if 2 * kk * (best_n // (2 * kk) + 1) <= moore]
            if not ks:
                break
            continue
        G = lo + rng.randrange(2)
        if 2 * k * G > moore:
            continue
        groups = _groups(G)
        if not groups:
            continue
        m, k2, r = rng.choice(groups)
        order, T = _table(m, k2, r)
        slice_end = min(deadline, time.monotonic() + per_try)
        res = _anneal(d, D, k, G, T, rng, slice_end)
        if res is not None:
            n, e = res
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
