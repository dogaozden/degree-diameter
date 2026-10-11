import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Multi-base voltage lifts, searched with a vectorised reachability cost.
#
# A lift has k left and k right base vertices over a group G (order |G| = G).
# It uses d layers. In layer L, left base vertex i is matched to right base
# vertex P[L, i] with voltage Gv[L, i]: A_{i,x} ~ B_{P,x*g}. Every layer is a
# perfect matching, so the graph is d-regular on 2kG vertices and bipartite.
#
# Left translation by G is an automorphism, so the diameter is checked from
# the 2k representatives A_{i,e} and B_{j,e} only. Each BFS step is a set of
# numpy fancy-indexing operations, one per layer, over all representatives.
# ----------------------------------------------------------------------------

_TABLES = {}


def _group_params(G):
    """All semidirect parameters (m, k, r) with m*k = G, giving Z_m x|_r Z_k."""
    out = []
    for gk in range(1, G + 1):
        if G % gk:
            continue
        gm = G // gk
        for r in range(gm):
            if math.gcd(r, gm) == 1 and pow(r, gk, gm) == 1 % gm:
                out.append((gm, gk, r))
    return out


def _table(m, k, r):
    """Cached (order, T) with T[x, y] = x*y for Z_m x|_r Z_k, element (a, b) coded as a*k+b."""
    key = (m, k, r)
    hit = _TABLES.get(key)
    if hit is not None:
        return hit
    order = m * k
    powers = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    xs = np.arange(order, dtype=np.int64)
    a = xs // k
    b = xs % k
    T = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    if len(_TABLES) > 40:
        _TABLES.clear()
    _TABLES[key] = (order, T)
    return order, T


def _anneal(d, D, k, G, T, rng, deadline, iters):
    """Anneal layer permutations and voltages to make a d-regular lift of diameter <= D.

    Returns (n, edges) if a valid lift is found, else None.
    """
    V = 2 * k * G
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    R = len(reps)
    rep_idx = np.arange(R)
    rep_arr = np.array(reps, dtype=np.int64)
    xs = np.arange(G, dtype=np.int64)

    P = np.array([rng.sample(range(k), k) for _ in range(d)], dtype=np.int64)
    Gv = np.array([[rng.randrange(G) for _ in range(k)] for _ in range(d)], dtype=np.int64)
    M = np.empty((d, V), dtype=np.int64)

    def fill(L):
        for i in range(k):
            a = i * G + xs
            b = (k + P[L, i]) * G + T[xs, Gv[L, i]]
            M[L, a] = b
            M[L, b] = a

    def cost():
        dup = 0
        for L1 in range(d):
            for L2 in range(L1 + 1, d):
                dup += int(np.count_nonzero(M[L1] == M[L2]))
        seen = np.zeros((R, V), dtype=bool)
        seen[rep_idx, rep_arr] = True
        front = seen.copy()
        for _ in range(D):
            nxt = np.zeros((R, V), dtype=bool)
            for L in range(d):
                nxt[:, M[L]] |= front  # M[L] is an involution, so indices are unique
            nxt &= ~seen
            if not nxt.any():
                break
            seen |= nxt
            front = nxt
        return 1000 * dup + (R * V - int(np.count_nonzero(seen)))

    for L in range(d):
        fill(L)
    cur = cost()
    T0 = max(1.0, 0.02 * cur)

    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - it / iters) + 0.3
        L = rng.randrange(d)
        oldP = P[L].copy()
        oldG = Gv[L].copy()
        oldM = M[L].copy()
        if k > 1 and rng.random() < 0.3:
            a, b = rng.sample(range(k), 2)
            P[L, a], P[L, b] = P[L, b], P[L, a]
        else:
            Gv[L, rng.randrange(k)] = rng.randrange(G)
        fill(L)
        c2 = cost()
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = c2
        else:
            P[L] = oldP
            Gv[L] = oldG
            M[L] = oldM

    if cur != 0:
        return None
    edges = set()
    for L in range(d):
        for v in range(V):
            w = int(M[L, v])
            if v < w:
                edges.add((v, w))
    return V, sorted(edges)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite with degree d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    best_n, best_e = best

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    moore = lib.moore_bound(d, D)

    # Projective plane incidence graph meets the Moore bound for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)

    if best_n >= moore:
        return best_n, best_e

    rng = random.Random(seed * 1000003 + d * 101 + D)

    # Search: aim for orders strictly above the current best.
    while time.monotonic() < deadline:
        feasible = [k for k in (1, 2, 3) if 2 * k * (best_n // (2 * k) + 1) <= moore]
        if not feasible:
            break
        k = rng.choice(feasible)
        Gmin = best_n // (2 * k) + 1
        G = Gmin + rng.randrange(0, 3)
        if 2 * k * G > moore:
            G = Gmin
        params = rng.choice(_group_params(G))
        _, T = _table(*params)
        remaining = deadline - time.monotonic()
        slice_t = max(0.5, min(6.0, remaining))
        res = _anneal(d, D, k, G, T, rng, time.monotonic() + slice_t, 6000)
        if res is not None:
            n, e = res
            consider(n, e)

    return best_n, best_e
