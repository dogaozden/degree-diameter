"""Bi-Cayley voltage-lift search with simulated annealing on the unreached-pair cost.

Targets: D >= 3 cases. Safe fallbacks: K_{d,d} (D >= 2), the 2D-cycle (d = 2),
and PG(2, d-1) incidence (D = 3, d-1 a prime power). Every returned graph is
checked with lib.is_valid, and the fallback is kept if a candidate fails.
"""
import math
import random
import time

import lib

_TABLE_CACHE = {}
ANNEAL_ITERS = 3000
GROUPS_PER_ORDER = 6


def _groups(N):
    """Semidirect parameters (m, k, r) with m * k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(m, k, r):
    """Cached (T, invs): T[x][g] = x*g, invs[g] = g^-1 for Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    if len(_TABLE_CACHE) >= 64:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = (T, invs)
    return T, invs


def _cost(N, T, invs, S, D):
    """Unreached (source, target) pairs within distance D, from A_0 and B_0.

    Bi-Cayley graph: A_x ~ B_{x g} for g in S. Left translation fixes each part,
    so these two eccentricity checks cover the whole graph.
    """
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _anneal(N, T, invs, d, D, rng, deadline, iters):
    """Simulated annealing over the connection set S (0 fixed in S). Returns S or None."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cost(N, T, invs, S, D)
    t_start, t_end = 1.5, 0.1
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = t_start * (t_end / t_start) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _cost(N, T, invs, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i] = old
    return S if cur == 0 else None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    deadline = t0 + budget

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and meets the Moore bound for D = 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    if D == 2:
        return fb_n, fb_e

    if d == 2:
        # Even cycle of length 2D: bipartite, 2-regular, diameter D (Moore bound).
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    moore = lib._moore_bound(d, D)
    best_n, best_e = fb_n, fb_e
    rng = random.Random(seed * 1000003 + d * 131 + D)

    while time.monotonic() < deadline and best_n < moore:
        lo = max(best_n // 2 + 1, d + 1)
        if 2 * lo > moore:
            break
        # Bias toward the smallest orders that would beat the current best.
        N = lo + int(rng.random() ** 2 * 40)
        if 2 * N > moore:
            N = moore // 2
        if N < lo:
            break

        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k, r in groups[:GROUPS_PER_ORDER]:
            if time.monotonic() > deadline:
                break
            T, invs = _table(m, k, r)
            S = _anneal(N, T, invs, d, D, rng, deadline, ANNEAL_ITERS)
            if S is not None:
                found = (T, S)
                break

        if found is not None:
            T, S = found
            n = 2 * N
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            if n > best_n and lib.is_valid(n, edges, d, D):
                best_n, best_e = n, edges

    if not lib.is_valid(best_n, best_e, d, D):
        return fb_n, fb_e
    return best_n, best_e
