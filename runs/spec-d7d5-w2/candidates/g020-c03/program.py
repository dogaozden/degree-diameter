import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: random bipartite d-regular graphs built from d permutations
# (layer l joins A_i to B_{P_l[i]}), repaired by annealing on transposition moves.
#
# Each layer is a permutation, so every vertex has degree d (duplicate edges can
# only lower the simple degree, never raise it). The cost is the number of ordered
# vertex pairs at distance > D, computed exactly with boolean reach matrices.
# A random-graph heuristic suggests that a d-regular bipartite graph on about
# 2 * s vertices has diameter D when the expected number of short walks per pair
# is large enough, so s is scanned from that estimate downwards for safety.
# ----------------------------------------------------------------------------

def _estimate_side(d, D):
    """Largest side size s for which the Poisson heuristic predicts few failing pairs."""
    lam = sum(d * (d - 1) ** (L - 1) for L in range(1, D + 1, 2))
    best = 3
    for s in range(3, 5000):
        if 2.0 * math.log(s) - lam / s < 0:
            best = s
    return best


def _cost(s, d, D, P):
    """Return (number of ordered pairs at distance > D, neighbour table) for layers P."""
    N = 2 * s
    nbr = np.empty((d, N), dtype=np.int64)
    nbr[:, :s] = s + P
    inv = np.empty((d, s), dtype=np.int64)
    rows = np.arange(d)[:, None]
    inv[rows, P] = np.arange(s, dtype=np.int64)[None, :]
    nbr[:, s:] = inv
    reach = np.eye(N, dtype=bool)
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return int(N * N - int(reach.sum())), nbr


def _anneal(s, d, D, rng, deadline):
    """Anneal layer permutations until every pair is within distance D; return P or None."""
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    cost, _ = _cost(s, d, D, P)
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)
    while cost > 0:
        now = time.monotonic()
        if now > deadline:
            break
        frac = (now - t_start) / span
        temp = max(0.5, 3.0 * (1.0 - frac))
        l = rng.randrange(d)
        i = rng.randrange(s)
        j = rng.randrange(s)
        if i == j:
            continue
        P[l, i], P[l, j] = P[l, j], P[l, i]
        c2, _ = _cost(s, d, D, P)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            P[l, i], P[l, j] = P[l, j], P[l, i]
    if cost == 0:
        return P
    return None


def _edges_from_layers(s, d, P):
    """Return (n, edges) for the bipartite graph A_i ~ B_{P_l[i]}, A = 0..s-1, B = s..2s-1."""
    es = set()
    for l in range(d):
        for i in range(s):
            es.add((i, s + int(P[l, i])))
    return 2 * s, sorted(es)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2 or d < 3:
        return best

    # Exact projective-plane construction for D = 3.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best

    # Bold change: random d-regular bipartite graphs repaired by annealing.
    rng = random.Random(seed)
    s_est = _estimate_side(d, D)
    for f in (0.7, 0.8, 0.88, 0.94):
        now = time.monotonic()
        rem = deadline - now
        if rem < 2.0:
            break
        s = max(3, int(f * s_est))
        if 2 * s <= best_n:
            continue
        attempt_deadline = now + rem * 0.5
        P = _anneal(s, d, D, rng, attempt_deadline)
        if P is not None:
            n, e = _edges_from_layers(s, d, P)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
