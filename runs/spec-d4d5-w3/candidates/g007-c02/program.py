"""Bi-Cayley voltage lifts over semidirect products, searched with bitset distance checks.

Fallbacks: K_{d,d} (diameter 2) and the projective plane PG(2, d-1) when D == 3.
Every candidate is checked with lib.is_valid before it replaces the best graph.
"""
import math
import random
import time

import lib

_BIG = 10 ** 9


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(60):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 80))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _table(G, mul):
    """Full multiplication table M[g][s] = g * s."""
    return [[mul(g, s) for s in range(G)] for g in range(G)]


def _cost(k, G, M, darts, D):
    """Number of ordered vertex pairs at distance > D. Zero means valid. Duplicate darts are forbidden."""
    N = 2 * k * G
    seen = set()
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        key = (i, j, s)
        if key in seen:
            return _BIG
        seen.add(key)
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + M[g][s]
            adj[a].append(b)
            adj[b].append(a)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _edges(k, G, M, darts):
    """Edge list of the lift: A-side vertices 0..kG-1, B-side vertices kG..2kG-1."""
    E = set()
    for i, j, s in darts:
        for g in range(G):
            E.add((i * G + g, (k + j) * G + M[g][s]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, M, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments. Returns darts or None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, M, darts, D)
    if cost == 0:
        return darts
    T0 = max(2.0, 0.05 * cost) if cost < _BIG else 50.0
    T_end = 0.3
    for t in range(iters):
        if (t & 15) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T_end / T0) ** (t / iters)
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, M, darts, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, M, darts, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
        if cost == 0:
            return darts
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed * 7919 + d * 101 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_e, d, D):
        return 2, [(0, 1)]

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if lib.is_prime_power(d - 1):
            return best_n, best_e

    if D == 2 or d < 2:
        return best_n, best_e

    # Main search: annealed bi-Cayley lifts, with the target order just above the best so far.
    ks = [1, 2, 3, 4]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        target = best_n + 2
        Gmin = -(-target // (2 * k))
        G = Gmin + rng.randrange(0, 3)
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        M = _table(order, mul)
        darts = _anneal(d, D, k, order, M, rng, deadline, iters=5000)
        if darts is None:
            continue
        n, e = _edges(k, order, M, darts)
        consider(n, e)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
