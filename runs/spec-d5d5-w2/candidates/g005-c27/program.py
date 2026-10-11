import math
import random
import time

import lib

BIG = 10 ** 9
_TABLE_CACHE = {}


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


def _table(m, k, r):
    """Cached (order, T) with T[g][s] = g*s for the semidirect product Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, _ = lib.semidirect_group(m, k, r)
    T = [[mul(g, s) for s in range(order)] for g in range(order)]
    if len(_TABLE_CACHE) > 64:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = (order, T)
    return order, T


def _cost(d, k, G, D, T, p, sv):
    """Number of (source, vertex) pairs at distance > D from the layer representatives.

    Lift: A-layer i, element g joins B-layer p[L][i], element g*sv[L][i] for each layer L.
    Left translation is an automorphism, so representatives A_{i,0} and B_{j,0} suffice.
    Returns BIG if two darts coincide (would create a multi-edge or a degree defect).
    """
    N = k * G
    total = 2 * N
    adj = [[] for _ in range(total)]
    keys = set()
    for L in range(d):
        pL = p[L]
        sL = sv[L]
        for i in range(k):
            j = pL[i]
            s = sL[i]
            key = (i, j, s)
            if key in keys:
                return BIG
            keys.add(key)
            bi = i * G
            bj = N + j * G
            for g in range(G):
                a = bi + g
                b = bj + T[g][s]
                adj[a].append(b)
                adj[b].append(a)
    sources = [i * G for i in range(k)] + [N + j * G for j in range(k)]
    bad = 0
    for src in sources:
        seen = bytearray(total)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        bad += total - cnt
    return bad


def _edges(d, k, G, T, p, sv):
    N = k * G
    E = set()
    for L in range(d):
        for i in range(k):
            j = p[L][i]
            s = sv[L][i]
            for g in range(G):
                E.add((i * G + g, N + j * G + T[g][s]))
    return 2 * N, sorted(E)


def _anneal(d, D, k, G, T, rng, slice_end):
    """Simulated annealing over voltages and layer permutations; returns (p, sv) on zero cost."""
    p = [rng.sample(range(k), k) for _ in range(d)]
    sv = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    cost = _cost(d, k, G, D, T, p, sv)
    tries = 0
    while cost >= BIG and tries < 100:
        sv = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
        cost = _cost(d, k, G, D, T, p, sv)
        tries += 1
    if cost >= BIG:
        return None

    start = time.monotonic()
    span = max(1e-3, slice_end - start)
    T0, T1 = 3.0, 0.2
    while cost > 0:
        now = time.monotonic()
        if now >= slice_end:
            break
        temp = T0 * (T1 / T0) ** min(1.0, (now - start) / span)
        if k == 1 or rng.random() < 0.75:
            L = rng.randrange(d)
            i = rng.randrange(k)
            old = sv[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            sv[L][i] = new
            c2 = _cost(d, k, G, D, T, p, sv)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                sv[L][i] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            pL = p[L]
            pL[a], pL[b] = pL[b], pL[a]
            c2 = _cost(d, k, G, D, T, p, sv)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                pL[a], pL[b] = pL[b], pL[a]

    if cost == 0:
        return p, sv
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite with degree d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    # Calibration: the projective plane meets the Moore bound when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Bi-Cayley / multi-base voltage lifts over semidirect products, annealed.
    # A k-base lift over a group of order G has 2*k*G vertices.
    slice_len = max(1.5, 0.08 * budget)
    while time.monotonic() < deadline - 0.5:
        if best[0] >= moore:
            break
        n_best = best[0]
        k = rng.choice((1, 1, 2, 3, 4))
        lo = n_best // (2 * k) + 1
        G = lo + rng.randrange(0, 4)
        if G < 2 or 2 * k * G > moore:
            continue
        m, k2, r = rng.choice(_groups(G))
        _, T = _table(m, k2, r)
        slice_end = min(deadline, time.monotonic() + slice_len)
        res = _anneal(d, D, k, G, T, rng, slice_end)
        if res is not None:
            n, e = _edges(d, k, G, T, res[0], res[1])
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
