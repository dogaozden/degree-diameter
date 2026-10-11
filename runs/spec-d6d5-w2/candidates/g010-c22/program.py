"""Bi-Cayley lift search with a matrix-based diameter cost.

Vertices are A_{i,g} and B_{j,g} for layers i, j in range(k) and g in a group
of order G. Each of the d layers is a permutation of range(k) with one
voltage per dart, so every vertex has degree d. Left multiplication by the
group is an automorphism, so checking distances from the 2k identity vertices
is exact. The cost (unreached (rep, vertex) pairs) is computed by repeated
float32 matrix products, which is much faster than Python BFS.

Fallbacks (K_2, cycle, K_{d,d}, projective plane incidence) are checked with
lib.is_valid before being returned.
"""
import math
import random
import time

import numpy as np

import lib


_GROUP_CACHE = {}
_TABLE_CACHE = {}


def _fallback(d, D):
    if d <= 0 or D <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        N = 2 * D
        return N, [(i, (i + 1) % N) for i in range(N)]
    return lib.haar_graph(d, range(d))


def _pg_candidate(d, D):
    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    return None


def _group_options(G):
    """All (m, k2, r) with Z_m x|_r Z_k2 of order G = m*k2 (r = 1 gives the direct product)."""
    if G in _GROUP_CACHE:
        return _GROUP_CACHE[G]
    out = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    _GROUP_CACHE[G] = out
    return out


def _table(m, k2, r):
    """T[s, g] = g * s in the semidirect product, as a numpy array."""
    key = (m, k2, r)
    if key in _TABLE_CACHE:
        return _TABLE_CACHE[key]
    order, mul, _ = lib.semidirect_group(m, k2, r)
    T = np.empty((order, order), dtype=np.int64)
    for s in range(order):
        for g in range(order):
            T[s, g] = mul(g, s)
    _TABLE_CACHE[key] = (order, T)
    return order, T


def _evaluate(k, G, D, T, src, tgt, volt, reps):
    """Number of (representative, vertex) pairs at distance > D. Zero means diameter <= D."""
    N = 2 * k * G
    M = np.zeros((N, N), dtype=np.float32)
    ar = np.arange(G)
    for t in range(len(src)):
        rows = src[t] * G + ar
        cols = (k + tgt[t]) * G + T[volt[t]]
        M[rows, cols] = 1.0
        M[cols, rows] = 1.0
    np.fill_diagonal(M, 1.0)
    R = np.zeros((len(reps), N), dtype=np.float32)
    R[np.arange(len(reps)), reps] = 1.0
    for _ in range(D):
        R = np.minimum(R @ M, 1.0)
    return len(reps) * N - int(round(float(R.sum())))


def _anneal(d, D, k, G, T, rng, deadline):
    """Simulated annealing over voltages and per-layer B-assignments.

    Returns (ok, src, tgt, volt).
    """
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    src = [i for _ in range(d) for i in range(k)]
    tgt = [0] * (d * k)
    for L in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            tgt[L * k + i] = p[i]
    volt = [rng.randrange(G) for _ in range(d * k)]

    cur = _evaluate(k, G, D, T, src, tgt, volt, reps)
    temp = 1.0
    while cur > 0 and time.monotonic() < deadline:
        temp = max(0.2, temp * 0.9995)
        if k > 1 and rng.random() < 0.3:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            tgt[ia], tgt[ib] = tgt[ib], tgt[ia]
            new = _evaluate(k, G, D, T, src, tgt, volt, reps)
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur = new
            else:
                tgt[ia], tgt[ib] = tgt[ib], tgt[ia]
        else:
            t = rng.randrange(d * k)
            old = volt[t]
            volt[t] = rng.randrange(G)
            new = _evaluate(k, G, D, T, src, tgt, volt, reps)
            if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
                cur = new
            else:
                volt[t] = old
    return cur == 0, src, tgt, volt


def _edges(k, G, T, src, tgt, volt):
    E = set()
    for t in range(len(src)):
        i, j, s = src[t], tgt[t], volt[t]
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + int(T[s, g])
            E.add((a, b))
    return 2 * k * G, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    if d <= 0 or D <= 0 or d <= 2 or D <= 2:
        # Small cases: fallbacks already meet the Moore bound or are trivial.
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    pg = _pg_candidate(d, D)
    if pg is not None:
        consider(pg[0], pg[1])

    moore = lib.moore_bound(d, D)
    ks = [1, 2, 3, 3, 4, 5, 6]

    while time.monotonic() < deadline and best[0] < moore:
        k = rng.choice(ks)
        base = best[0] // (2 * k)
        G = base + 1 + rng.randrange(3)
        groups = _group_options(G)
        if not groups:
            continue
        m, k2, r = rng.choice(groups)
        order, T = _table(m, k2, r)
        slice_end = min(deadline, time.monotonic() + 4.0)
        ok, src, tgt, volt = _anneal(d, D, k, order, T, rng, slice_end)
        if ok:
            n, e = _edges(k, order, T, src, tgt, volt)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d, D)
    return best
