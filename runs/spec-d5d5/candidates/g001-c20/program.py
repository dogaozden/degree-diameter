import math
import random
import time

import numpy as np

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Baseline: projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group sampling and permutation tables.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul), or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 8])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _perm_table(G, mul):
    """pt[s][g] = g * s as numpy arrays, so each right translation is precomputed once."""
    return [np.array([mul(g, s) for g in range(G)], dtype=np.int64) for s in range(G)]


# ----------------------------------------------------------------------------
# NEW HELPER: matrix-power reachability over orbit representatives.
#
# The lift is invariant under left multiplication by the group, so the graph is
# vertex-transitive inside each base class. It therefore suffices to check the
# balls of one representative per base vertex (2k of them). We compute all those
# balls at once with a float matrix product:  R <- min(R + R @ A, 1), D times.
# ----------------------------------------------------------------------------

def _adjacency(k, G, layers, pt):
    N = 2 * k * G
    A = np.zeros((N, N), dtype=np.float32)
    ar = np.arange(G, dtype=np.int64)
    for lay in layers:
        for i, (j, s) in enumerate(lay):
            rows = i * G + ar
            cols = (k + j) * G + pt[s]
            A[rows, cols] = 1.0
            A[cols, rows] = 1.0
    return A


def _cost(k, G, D, layers, pt):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    keys = set()
    for lay in layers:
        for i, (j, s) in enumerate(lay):
            key = (i, j, s)
            if key in keys:
                return _BIG
            keys.add(key)
    N = 2 * k * G
    A = _adjacency(k, G, layers, pt)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    R = np.zeros((len(reps), N), dtype=np.float32)
    R[np.arange(len(reps)), reps] = 1.0
    for _ in range(D):
        R = np.minimum(R + R @ A, 1.0)
    return int(len(reps) * N - round(float(R.sum())))


def _edges(k, G, layers, pt):
    E = set()
    for lay in layers:
        for i, (j, s) in enumerate(lay):
            pm = pt[s]
            for g in range(G):
                E.add((i * G + g, (k + j) * G + int(pm[g])))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Annealing over voltages and per-layer base permutations.
#
# A layer is a list over base A-indices i of (j, s): A_i,g joins B_j,g*s.
# Each layer is a permutation i -> j, so every base vertex has degree d.
# ----------------------------------------------------------------------------

def _anneal(k, G, D, d, layers, pt, rng, deadline, iters):
    cost = _cost(k, G, D, layers, pt)
    if cost >= _BIG:
        return cost
    T0 = max(0.5, 0.08 * cost)
    T_end = 0.3
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)
        if k == 1 or rng.random() < 0.75:
            L = rng.randrange(d)
            i = rng.randrange(k)
            j, old = layers[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            layers[L][i] = (j, new)
            c2 = _cost(k, G, D, layers, pt)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                layers[L][i] = (j, old)
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            (ja, sa), (jb, sb) = layers[L][a], layers[L][b]
            layers[L][a] = (jb, sa)
            layers[L][b] = (ja, sb)
            c2 = _cost(k, G, D, layers, pt)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                layers[L][a] = (ja, sa)
                layers[L][b] = (jb, sb)
    return cost


# ----------------------------------------------------------------------------
# NEW IDEA: warm-started base growth.
#
# For a fixed group of order G, solve k = 1 first. Then repeatedly add one new
# base pair (A_k, B_k) to every layer: the permutations extend by k -> k, so the
# lift stays d-regular with 2G more vertices. The new state is annealed from a
# near-valid warm start instead of from random voltages. Growth stops when two
# attempts fail. Every success is a valid candidate of order 2kG.
# ----------------------------------------------------------------------------

def _grow_search(d, D, G, pt, rng, deadline, consider):
    if G < d:
        return
    layers = [[(0, s)] for s in rng.sample(range(G), d)]
    k = 1
    if _anneal(k, G, D, d, layers, pt, rng, deadline, 600) != 0:
        return
    n, e = _edges(k, G, layers, pt)
    consider(n, e)
    while time.monotonic() < deadline:
        base = [list(lay) for lay in layers]
        ok = False
        for attempt in range(2):
            cur = [list(lay) for lay in base]
            new_s = rng.sample(range(G), d)
            for L, lay in enumerate(cur):
                lay.append((k, new_s[L]))
            if _anneal(k + 1, G, D, d, cur, pt, rng, deadline,
                       350 + 250 * attempt) == 0:
                ok = True
                layers = cur
                break
        if not ok:
            return
        k += 1
        n, e = _edges(k, G, layers, pt)
        consider(n, e)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.85 * time_limit, time_limit - 3.0)
    budget = max(0.2 * time_limit, budget)
    deadline = start + budget
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
            # PG(2, d-1) meets the Moore bound for D = 3: nothing to search for.
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 3:
        lo = max(d + 1, 6)
        hi = max(200, best_n // 2 + 40)
        while time.monotonic() < deadline:
            G = rng.randint(lo, hi)
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            pt = _perm_table(order, mul)
            _grow_search(d, D, order, pt, rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
