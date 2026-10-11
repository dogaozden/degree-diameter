import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baseline: incidence graph of PG(2, q) for the largest prime power q + 1 <= d.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW HELPER 1: vectorised multiplication table of Z_m x|_r Z_k2.
# The whole table is built with numpy, so right multiplication by any s is a
# single column lookup T[:, s] instead of a Python loop over the group.
# ----------------------------------------------------------------------------

def _semidirect_table(m, k2, r):
    G = m * k2
    X = np.arange(G, dtype=np.int64)
    a = X // k2
    b = X % k2
    pw = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    # (a, b) * (c, d) = (a + r^b c, b + d)
    table = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k2 \
        + (b[:, None] + b[None, :]) % k2
    return table


def _group_choices(G, rng, cap=60):
    """Semidirect groups Z_m x| Z_k2 of order G, shuffled and capped."""
    out = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if k2 == 1:
            out.append((m, 1, 1))
            continue
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    rng.shuffle(out)
    return out[:cap]


# ----------------------------------------------------------------------------
# NEW HELPER 2: matrix-based ball cost.
# Bi-Cayley lifts are vertex-transitive within each base class, so only the
# 2k base representatives need checking. Balls are propagated as a (R x N)
# 0/1 float matrix: Ball_{t+1} = min(Ball_t + Ball_t @ M, 1). This avoids
# Python BFS queues entirely.
# Returns the number of (representative, vertex) pairs at distance > D.
# ----------------------------------------------------------------------------

_BIG = 10 ** 6


def _cost(k, G, D, darts, T):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG  # repeated darts waste degree
    N = 2 * k * G
    M = np.zeros((N, N), dtype=np.float32)
    ar = np.arange(G)
    for i, j, s in darts:
        A = i * G + ar
        B = (k + j) * G + T[:, s]
        M[A, B] = 1.0
        M[B, A] = 1.0
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    R = len(reps)
    Bm = np.zeros((R, N), dtype=np.float32)
    Bm[np.arange(R), reps] = 1.0
    for _ in range(D):
        Bm = np.minimum(Bm + Bm @ M, 1.0)
    return int(R * N - Bm.sum())


def _edges(k, G, darts, T):
    E = []
    ar = np.arange(G)
    for i, j, s in darts:
        A = i * G + ar
        B = (k + j) * G + T[:, s]
        E.extend(zip(A.tolist(), B.tolist()))
    return 2 * k * G, sorted(set(E))


# ----------------------------------------------------------------------------
# NEW IDEA: identity normalisation plus simulated annealing.
# For k = 1 the map B_h -> B_{h t} (for any t) is an isomorphism that shifts
# every voltage s to s*t. So the first dart can be fixed to the identity,
# which removes one whole group-sized dimension from the search. The rest of
# the voltages are annealed with a Metropolis acceptance on the unreached-pair
# count, with a linearly cooling temperature.
# ----------------------------------------------------------------------------

def _anneal(k, G, d, D, T, rng, iters, deadline):
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, layers[l][i], rng.randrange(G)] for l in range(d) for i in range(k)]
    fixed = 0 if k == 1 else -1
    if k == 1:
        darts[0][2] = 0
    cost = _cost(k, G, D, darts, T)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        idx = rng.randrange(len(darts))
        if idx == fixed:
            continue
        temp = 1.5 * (1.0 - t / iters) + 0.05
        old = darts[idx][2]
        darts[idx][2] = rng.randrange(G)
        c2 = _cost(k, G, D, darts, T)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            darts[idx][2] = old
    return cost, darts


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    moore = lib._moore_bound(d, D)
    if best_n >= moore or d < 3 or D < 3:
        return best

    # Main search over bi-Cayley lifts. k = 1 is weighted heavily for D = 5.
    while time.monotonic() < deadline:
        k = 1 if rng.random() < 0.85 else 2
        lo = best_n // (2 * k) + 1          # aim strictly above current best
        G = lo + rng.randrange(0, 6 if k == 1 else 10)
        if 2 * k * G > moore:
            continue
        groups = _group_choices(G, rng)
        for m, k2, r in groups[:3]:
            if time.monotonic() > deadline:
                break
            T = _semidirect_table(m, k2, r)
            cost, darts = _anneal(k, G, d, D, T, rng, 3000, deadline)
            if cost == 0:
                n, E = _edges(k, G, darts, T)
                if n > best_n:
                    consider(n, E)
                break

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
