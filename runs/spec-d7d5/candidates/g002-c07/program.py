import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bold construction: annealed random d-regular bipartite graphs.
#
# A graph on parts A = {0..m-1}, B = {m..2m-1} is given by d permutations
# P[0..d-1] of range(m): layer k joins a to m + P[k][a]. Every vertex then has
# degree exactly d. Cost = (unordered pairs at distance > D) + penalty * (duplicate
# edges). Simulated annealing swaps two entries inside one layer, which keeps
# every layer a permutation. Graphs are then verified with lib.is_valid.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)
_PEN = 40.0


def _cost(P, d, D):
    m = P.shape[1]
    n = 2 * m
    Q = np.empty_like(P)
    Q[np.arange(d)[:, None], P] = np.arange(m)[None, :]
    # adj[v, k] = neighbour of v in layer k (A rows first, then B rows).
    adj = np.concatenate([m + P.T, Q.T], axis=0)
    R = np.packbits(np.eye(n, dtype=bool), axis=1)  # bitset balls, radius 0
    for _ in range(D):
        R = R | np.bitwise_or.reduce(R[adj], axis=1)
    covered = int(_POP8[R].sum())
    bad = (n * n - covered) // 2
    dup = int(np.count_nonzero(P[:, None, :] == P[None, :, :]))
    conf = (dup - d * m) // 2
    return bad + _PEN * conf


def _anneal(m, d, D, nprng, pyrng, deadline, iters):
    P = np.array([nprng.permutation(m) for _ in range(d)], dtype=np.int64)
    cost = _cost(P, d, D)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        k = pyrng.randrange(d)
        a1, a2 = pyrng.sample(range(m), 2)
        P[k, a1], P[k, a2] = P[k, a2], P[k, a1]
        c2 = _cost(P, d, D)
        temp = 1.5 * (1.0 - t / iters) + 0.05
        if c2 <= cost or pyrng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            P[k, a1], P[k, a2] = P[k, a2], P[k, a1]
    return P if cost == 0 else None


def _edges_from(P, d, m):
    E = set()
    for k in range(d):
        for a in range(m):
            E.add((a, m + int(P[k, a])))
    return sorted(E)


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 6.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2, optimal for D = 2).
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = (fb_n, fb_e)
    if D == 2 or d == 1:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact projective-plane incidence graph when d-1 is a prime power (D = 3).
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                if q == d - 1:
                    return best
                break

    nprng = np.random.default_rng(seed)
    pyrng = random.Random(seed * 1000003 + d * 31 + D)

    lo = 0        # largest m with a verified graph
    hi = None     # smallest m that failed (after a success exists)
    m = max(d + 1, best[0] // 2 + 1)
    slice_len = max(4.0, budget / 6.0)

    while time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.5:
            break
        slice_end = now + min(remaining, slice_len)
        P = _anneal(m, d, D, nprng, pyrng, slice_end, 2000)
        if P is not None:
            e = _edges_from(P, d, m)
            consider(2 * m, e)
            lo = m
            if hi is None:
                m = int(m * 1.1) + 1
            else:
                if hi - lo <= 1:
                    break
                m = (lo + hi) // 2
        else:
            if lo == 0:
                # Nothing succeeded yet: retry the same size with fresh randomness.
                continue
            hi = m
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = (fb_n, fb_e)
    return best
