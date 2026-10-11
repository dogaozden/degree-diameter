import math
import random
import time

import numpy as np

import lib

BIG = 10 ** 9
ANNEAL_ITERS = 2500
KS = (1, 2, 2, 3, 4)
_GROUPS_CACHE = {}
_RP_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k2, r) with m * k2 = N, giving Z_m x|_r Z_k2."""
    hit = _GROUPS_CACHE.get(N)
    if hit is not None:
        return hit
    out = []
    for k2 in range(1, N + 1):
        if N % k2:
            continue
        m = N // k2
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    if len(_GROUPS_CACHE) > 64:
        _GROUPS_CACHE.clear()
    _GROUPS_CACHE[N] = out
    return out


def _right_table(m, k2, r):
    """Return (order, RP) with RP[s, g] = g * s in the group Z_m x|_r Z_k2."""
    key = (m, k2, r)
    hit = _RP_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, _ = lib.semidirect_group(m, k2, r)
    RP = np.array([[mul(g, s) for g in range(order)] for s in range(order)],
                  dtype=np.int64)
    val = (order, RP)
    if len(_RP_CACHE) > 48:
        _RP_CACHE.clear()
    _RP_CACHE[key] = val
    return val


def _cost(k, G, D, darts, RP):
    """Number of (base representative, vertex) pairs not within distance D.

    Lift vertices: A_{i,g} = i*G+g, B_{j,g} = (k+j)*G+g. Dart (i, j, s) joins
    A_{i,g} to B_{j, g*s}. Left translation by the group is an automorphism,
    so one representative per base vertex suffices. Zero means valid.
    """
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return BIG
    N = 2 * k * G
    A = np.zeros((N, N), dtype=np.float32)
    ar = np.arange(G, dtype=np.int64)
    for i, j, s in darts:
        u = i * G + ar
        v = (k + j) * G + RP[s]
        A[u, v] = 1.0
        A[v, u] = 1.0
    R = 2 * k
    F = np.zeros((N, R), dtype=np.float32)
    F[np.arange(R) * G, np.arange(R)] = 1.0
    seen = F > 0
    for _ in range(D):
        nxt = (A @ F) > 0
        new = nxt & ~seen
        if not new.any():
            break
        seen |= new
        F = new.astype(np.float32)
    return int(N * R - np.count_nonzero(seen))


def _edges(k, G, darts, RP):
    E = set()
    for i, j, s in darts:
        for g in range(G):
            E.add((i * G + g, (k + j) * G + int(RP[s, g])))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, RP, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer target permutations.

    Each of the d layers is a permutation p of the k base vertices; the darts
    (i, p[i], s) give a d-regular bipartite lift on 2*k*G vertices.
    """
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, D, darts, RP)

    T0 = max(1.0, 0.05 * cost) if cost < BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, RP)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, RP)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, RP)
    return None


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)
    rng = random.Random(seed * 1000003 + d * 101 + D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: multi-base voltage lifts over semidirect groups, annealed
    # with a numpy-vectorised reachability cost. Aim strictly above the best order.
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        k = rng.choice(KS)
        lo = n_best // (2 * k) + 1
        G = lo + rng.randrange(0, max(1, lo // 25) + 1)
        if 2 * k * G > moore:
            continue
        groups = _groups(G)
        if not groups:
            continue
        m, k2, r = rng.choice(groups)
        order, RP = _right_table(m, k2, r)
        res = _anneal(d, D, k, order, RP, rng, deadline, ANNEAL_ITERS)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
