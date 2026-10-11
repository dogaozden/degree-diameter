"""Bi-cyclic / semidirect voltage lifts with annealed voltages, validated by bit-parallel BFS.

Approach for the D >= 4 search (the target d=5, D=5 case):
  * A base bipartite graph with k vertices per side and d layers. Layer L is a
    perfect matching sigma_L between base sides, and each dart carries a voltage
    g_L(i) in a group G of order G. The lift has 2*k*G vertices and is d-regular.
  * The group is a semidirect product Z_m x|_r Z_k2 (lib.semidirect_group), so
    cyclic groups are included as the special case k2 = 1.
  * Simulated annealing moves voltages and swaps matching entries. The cost is
    the number of unordered vertex pairs at distance > D, plus a large penalty
    for duplicate darts (which would lower degrees or create multi-edges).
  * Orders are pushed upward from the current best. Every accepted graph is
    checked with lib.is_valid before it replaces the best.

Fallbacks: K_{d,d} always, and PG(2, d-1) incidence for D = 3 when d-1 is a
prime power. Nothing is returned unless it passes lib.is_valid.

Not benchmarked here.
"""
import math
import random
import time

import lib


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(order, mul):
    """T[x][g] = x * g for all group elements."""
    return [[mul(x, g) for g in range(order)] for x in range(order)]


def _lift_cost(d, D, k, G, T, sig, gv):
    """Unordered pairs at distance > D in the lift, plus a penalty per duplicate dart."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    seen = set()
    dups = 0
    for L in range(d):
        sL = sig[L]
        gL = gv[L]
        for i in range(k):
            j = sL[i]
            g = gL[i]
            key = (i, j, g)
            if key in seen:
                dups += 1
            else:
                seen.add(key)
            ba = i * G
            bb = (k + j) * G
            for x in range(G):
                a = ba + x
                b = bb + T[x][g]
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
    unreached = sum(N - r.bit_count() for r in reach) // 2
    return unreached + 1000 * dups


def _lift_anneal(d, D, k, G, T, rng, deadline):
    """Anneal voltages and matchings for one lift order. Returns (n, edges) or None."""
    sig = [rng.sample(range(k), k) for _ in range(d)]
    gv = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    cur = _lift_cost(d, D, k, G, T, sig, gv)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        temp = 1.0 + (0.15 - 1.0) * frac
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.5:
            i = rng.randrange(k)
            old = gv[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            gv[L][i] = new
            c2 = _lift_cost(d, D, k, G, T, sig, gv)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cur = c2
            else:
                gv[L][i] = old
        else:
            a, b = rng.sample(range(k), 2)
            sig[L][a], sig[L][b] = sig[L][b], sig[L][a]
            c2 = _lift_cost(d, D, k, G, T, sig, gv)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cur = c2
            else:
                sig[L][a], sig[L][b] = sig[L][b], sig[L][a]
    if cur != 0:
        return None
    edges = []
    for L in range(d):
        for i in range(k):
            j = sig[L][i]
            g = gv[L][i]
            for x in range(G):
                edges.append((i * G + x, (k + j) * G + T[x][g]))
    return 2 * k * G, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if best_n < n <= moore and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured baseline for D = 3: projective plane of order d-1.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n_pg, e_pg = lib.projective_plane_incidence(d - 1)
        consider(n_pg, e_pg)

    # Main search: symmetric lifts with k base vertices per side over a group of order G.
    while best_n < moore and time.monotonic() < deadline - 0.5:
        ks = [k for k in (1, 2, 3, 4, 5, 6) if 2 * k * (best_n // (2 * k) + 1) <= moore]
        if not ks:
            break
        k = rng.choice(ks)
        G = best_n // (2 * k) + 1 + rng.randrange(2)
        if 2 * k * G > moore:
            G = best_n // (2 * k) + 1
        groups = _groups(G)
        m, k2, r = rng.choice(groups)
        order, mul, _ = lib.semidirect_group(m, k2, r)
        T = _table(order, mul)
        remaining = deadline - time.monotonic()
        slice_t = min(remaining, max(2.0, 0.2 * budget))
        res = _lift_anneal(d, D, k, G, T, rng, time.monotonic() + slice_t)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
