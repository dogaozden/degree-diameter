"""Bi-Cayley lift search for bipartite graphs with max degree d and diameter D.

Construction: for a group G = Z_m x|_r Z_k of order N, the bi-Cayley graph has
parts A = {A_x} and B = {B_y} with A_x ~ B_{x*g} for g in S, |S| = d. Left
translation is an automorphism, so the diameter can be checked from A_0 and B_0.
S is searched by simulated annealing over the number of unreached pairs, using
vectorised numpy BFS. The search sweeps the group order N upward from the
smallest order that beats the current best, and every result is re-validated
with lib.is_valid before it is accepted. The fallback is K_{d,d}, which has
diameter 2 and is valid for every D >= 2.
"""
import math
import random
import time

import numpy as np

import lib

_TABLE_CACHE = {}
_SLICE = 0.8  # seconds of annealing per (order, group) attempt


def _kdd(d):
    """K_{d,d}: valid for every D >= 2, with 2d vertices."""
    if d < 1:
        return 1, []
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


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


def _tables(m, k, r):
    """Cached (order, T, invs): T[x, g] = x*g and invs[g] = g^-1, as numpy arrays."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = np.array([[mul(x, g) for g in range(order)] for x in range(order)], dtype=np.int64)
    invs = np.array([inv(g) for g in range(order)], dtype=np.int64)
    if len(_TABLE_CACHE) >= 32:
        _TABLE_CACHE.clear()
    val = (order, T, invs)
    _TABLE_CACHE[key] = val
    return val


def _cost(N, T, S, Sinv, D):
    """Pairs (source, vertex) not within distance D, from A_0 and B_0. Zero means valid."""
    total = 0
    for src in (0, N):
        seen = np.zeros(2 * N, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            a = front[front < N]
            b = front[front >= N] - N
            parts = []
            if a.size:
                parts.append(N + T[np.ix_(a, S)].ravel())   # A_x -> B_{x g}
            if b.size:
                parts.append(T[np.ix_(b, Sinv)].ravel())    # B_y -> A_{y g^-1}
            if not parts:
                break
            mask = np.zeros(2 * N, dtype=bool)
            mask[np.concatenate(parts)] = True
            mask &= ~seen
            if not mask.any():
                break
            seen |= mask
            front = np.flatnonzero(mask)
        total += 2 * N - int(seen.sum())
    return total


def _search(N, T, invs, d, D, rng, t_end):
    """Anneal a connection set S (identity fixed in S, WLOG) to zero cost. Returns S or None."""
    S = [0] + rng.sample(range(1, N), d - 1)
    Sa = np.array(S, dtype=np.int64)
    cur = _cost(N, T, Sa, invs[Sa], D)
    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    Ta, Tb = 3.0, 0.2
    while cur > 0:
        now = time.monotonic()
        if now >= t_end:
            break
        temp = Ta * (Tb / Ta) ** min(1.0, (now - t0) / span)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        Sb = np.array(S2, dtype=np.int64)
        v = _cost(N, T, Sb, invs[Sb], D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _kdd(d)
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Projective-plane baseline for diameter 3.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n2, e2 = lib.projective_plane_incidence(q)
                consider(n2, e2)
                break

    if best[0] >= moore or d < 2:
        return best

    rng = random.Random(seed * 1000003 + 97 * d + D)
    N_hi = moore // 2
    N = max(best[0] // 2 + 1, d)

    while time.monotonic() < deadline and best[0] < moore:
        if N > N_hi:
            N = max(best[0] // 2 + 1, d)
            if N > N_hi:
                break
        groups = _groups(N)
        nonab = [g for g in groups if g[1] > 1 and g[2] != 1 % g[0]]
        pool = nonab if nonab else groups
        rng.shuffle(pool)
        found = None
        for m, k2, r in pool[:2]:
            if time.monotonic() >= deadline:
                break
            _, T, invs = _tables(m, k2, r)
            t_end = min(deadline, time.monotonic() + _SLICE)
            S = _search(N, T, invs, d, D, rng, t_end)
            if S is not None:
                found = (T, S)
                break
        if found is not None:
            T, S = found
            edges = [(x, N + int(T[x, g])) for x in range(N) for g in S]
            consider(2 * N, edges)
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = _kdd(d)
    return best


def build(d, D, seed, time_limit):
    try:
        return _build(d, D, seed, time_limit)
    except Exception:
        return _kdd(d) if (d >= 1 and D >= 2) else ((1, []) if d < 1 or D < 1 else (2, [(0, 1)]))
