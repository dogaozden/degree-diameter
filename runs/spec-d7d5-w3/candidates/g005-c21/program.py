import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baseline: incidence graph of PG(2, q) for the largest prime power q
# with q + 1 <= d. Diameter 3, degree q + 1 <= d.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: edge-permutation search on d-regular bipartite graphs.
#
# A bipartite graph with parts A = {0..h-1} and B = {h..2h-1} is described by
# d permutations P[l] of {0..h-1}: A-vertex i is joined to B-vertex h + P[l][i]
# for every layer l. Each layer is a perfect matching, so the graph is d-regular
# and bipartite by construction. Duplicate edges appear as repeated values in a
# column of P and are penalised.
#
# Cost = (ordered pairs at distance > D) + PENALTY * (duplicate edges).
# Moves swap two targets inside one layer, which keeps all permutations valid.
# Simulated annealing runs at the current order h. When cost reaches 0 the
# graph is recorded and grown by one vertex per side: each layer is extended
# and the new A/B pair is spliced into a random position, then the search
# continues from the inherited state.
# ----------------------------------------------------------------------------

_PEN = 20
_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _evaluate(P, D):
    """Return (cost, inv, pop). pop[v] = number of vertices within distance D of v (including v)."""
    d, h = P.shape
    N = 2 * h
    rows = np.arange(d)[:, None]
    inv = np.empty_like(P)
    inv[rows, P] = np.arange(h, dtype=np.int64)[None, :]
    nbr = np.empty((N, d), dtype=np.int64)
    nbr[:h] = P.T + h
    nbr[h:] = inv.T

    W = (N + 63) // 64
    idx = np.arange(N, dtype=np.int64)
    reach = np.zeros((N, W), dtype=np.uint64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[nbr], axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    pop = _POP8[reach.view(np.uint8)].sum(axis=1)
    unreached = N * N - int(pop.sum())
    S = np.sort(P, axis=0)
    dup = int(np.sum(S[1:] == S[:-1]))
    return unreached + _PEN * dup, inv, pop


def _grow(P, d, rng):
    """Extend a d-layer permutation system from h to h+1 on each side, keeping every layer a bijection."""
    h = P.shape[1]
    newP = np.empty((d, h + 1), dtype=np.int64)
    for l in range(d):
        row = np.empty(h + 1, dtype=np.int64)
        row[:h] = P[l]
        row[h] = h
        i = rng.randrange(h)
        row[h] = row[i]
        row[i] = h
        newP[l] = row
    return newP


def _search(d, D, rng, deadline):
    """Anneal with growth. Returns the largest permutation system with cost 0 found, or None."""
    h = max(d, 2)
    P = np.array([rng.sample(range(h), h) for _ in range(d)], dtype=np.int64)
    cost, inv, pop = _evaluate(P, D)
    best = None
    T = 1.5
    while time.monotonic() < deadline:
        if cost == 0:
            best = P.copy()
            P = _grow(P, d, rng)
            h += 1
            cost, inv, pop = _evaluate(P, D)
            continue
        l = rng.randrange(d)
        if rng.random() < 0.5:
            bad = np.flatnonzero(pop < 2 * h)
            if bad.size:
                v = int(bad[rng.randrange(bad.size)])
                i = v if v < h else int(inv[l, v - h])
            else:
                i = rng.randrange(h)
        else:
            i = rng.randrange(h)
        j = rng.randrange(h)
        if i == j:
            continue
        P[l, i], P[l, j] = P[l, j], P[l, i]
        c2, inv2, pop2 = _evaluate(P, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost, inv, pop = c2, inv2, pop2
        else:
            P[l, i], P[l, j] = P[l, j], P[l, i]
    return best


def _edges_from(P):
    d, h = P.shape
    return 2 * h, [(i, h + int(P[l, i])) for i in range(h) for l in range(d)]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, time_limit - 6.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best_n and lib.is_valid(pg[0], pg[1], d, D):
            best_n, best_e = pg
        if D == 3 and lib.is_prime_power(d - 1):
            return best_n, best_e

    if D >= 3:
        rng = random.Random(seed)
        P = _search(d, D, rng, deadline)
        if P is not None:
            n, e = _edges_from(P)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_e = n, e

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
