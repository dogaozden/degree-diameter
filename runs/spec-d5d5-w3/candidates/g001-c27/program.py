"""Bi-Cayley lift search with a numpy-accelerated diameter cost.

Family: A_x ~ B_{x*g} for g in S over semidirect groups Z_m x|_r Z_k of order N.
The search sweeps N upward from the current best, annealing S to zero unreached
pairs. Every candidate is checked with lib.is_valid before it replaces the best.
Fallbacks: K_{d,d} always, and the projective-plane incidence graph when D = 3
and d-1 is a prime power.
"""
import math
import random
import time

import numpy as np

import lib

ITERS = 1500        # annealing steps per (N, group) attempt
MAX_GROUPS = 12     # groups tried per order N per sweep
_GROUP_CACHE = {}


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
    """Cached (order, T, invs): T[x][g] = x*g as a numpy array, invs[g] = g^-1."""
    key = (m, k, r)
    hit = _GROUP_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = np.array([[mul(x, g) for g in range(order)] for x in range(order)], dtype=np.int64)
    invs = np.array([inv(g) for g in range(order)], dtype=np.int64)
    val = (order, T, invs)
    if len(_GROUP_CACHE) > 64:
        _GROUP_CACHE.clear()
    _GROUP_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Number of (source, vertex) pairs not within distance D, sources A_0 and B_0."""
    S = np.asarray(S, dtype=np.int64)
    Sinv = invs[S]
    total = 0
    for src in (0, N):
        seen = np.zeros(2 * N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            fa = frontier[frontier < N]
            fb = frontier[frontier >= N] - N
            parts = []
            if fa.size:
                parts.append(N + T[fa][:, S].ravel())   # A_x -> B_{x g}
            if fb.size:
                parts.append(T[fb][:, Sinv].ravel())    # B_y -> A_{y g^-1}
            if not parts:
                break
            cand = np.concatenate(parts)
            cand = cand[~seen[cand]]
            if cand.size == 0:
                break
            cand = np.unique(cand)
            seen[cand] = True
            frontier = cand
        total += 2 * N - int(seen.sum())
    return total


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if (it & 7) == 0 and time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, bipartite, degree d, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best_e = list(best_e)
    if D == 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    # D = 3 with d-1 a prime power: projective plane incidence graph meets the Moore bound.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        if lib.is_valid(best_n, best_e, d, D):
            return best_n, best_e

    moore = lib.moore_bound(d, D)
    Nmax = moore // 2
    N = best_n // 2 + 1

    # Sweep N upward; stay on N until a valid lift is found or time runs out.
    while time.monotonic() < deadline and N <= Nmax and N > d:
        groups = _groups(N)
        rng.shuffle(groups)
        found = False
        for m, k, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            _, T, invs = _table(m, k, r)
            S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
            if S is None:
                continue
            edges = [(x, N + int(T[x, g])) for x in range(N) for g in S]
            if consider(2 * N, edges):
                found = True
                break
        if found:
            N = best_n // 2 + 1

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
        best_e = list(best_e)
    return best_n, best_e
