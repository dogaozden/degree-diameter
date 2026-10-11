import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Multi-base lifts over arbitrary finite groups of the form Z_m x|_r Z_k2.
# Search uses numpy boolean frontiers (one per base block) instead of Python
# BFS, so each candidate is scored by a few hundred vectorised operations.
#
# Graph: k base vertices per side, group G. d layers; layer L pairs A_i with
# B_{P[L][i]} via voltage V[L][i]. Edge A_i(x) -- B_j(x*s) for each dart.
# Left translation is an automorphism, so BFS from A_i(e) and B_j(e) suffices.
# ----------------------------------------------------------------------------

_PEN = 2
_TABLE_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k2, r) with m*k2 = N and Z_m x|_r Z_k2 valid."""
    out = []
    for k2 in range(1, N + 1):
        if N % k2:
            continue
        m = N // k2
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    return out


def _group_cols(m, k2, r):
    """Return (order, cols) where cols[s][x] = x * s (right multiplication permutations)."""
    key = (m, k2, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, _ = lib.semidirect_group(m, k2, r)
    cols = [np.array([mul(x, s) for x in range(order)], dtype=np.intp)
            for s in range(order)]
    val = (order, cols)
    if len(_TABLE_CACHE) >= 64:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(k, G, D, pdarts):
    """Total number of (source, vertex) pairs not reached within D, over all 2k block sources."""
    full = 2 * k * G
    total = 0
    for side in (0, 1):
        for src in range(k):
            RA = [np.zeros(G, dtype=bool) for _ in range(k)]
            RB = [np.zeros(G, dtype=bool) for _ in range(k)]
            if side == 0:
                RA[src][0] = True
            else:
                RB[src][0] = True
            fA = [a.copy() for a in RA]
            fB = [b.copy() for b in RB]
            reached = 1
            for _ in range(D):
                nA = [np.zeros(G, dtype=bool) for _ in range(k)]
                nB = [np.zeros(G, dtype=bool) for _ in range(k)]
                for i, j, p in pdarts:
                    if fA[i].any():
                        nB[j][p] |= fA[i]
                    if fB[j].any():
                        nA[i] |= fB[j][p]
                new = 0
                for j in range(k):
                    nB[j] &= ~RB[j]
                    RB[j] |= nB[j]
                    new += int(np.count_nonzero(nB[j]))
                for i in range(k):
                    nA[i] &= ~RA[i]
                    RA[i] |= nA[i]
                    new += int(np.count_nonzero(nA[i]))
                reached += new
                if new == 0:
                    break
                fA, fB = nA, nB
            total += full - reached
    return total


def _cost(k, G, D, darts, cols):
    """Unreached pairs plus a penalty for duplicate darts. Zero means valid."""
    dup = len(darts) - len(set(darts))
    pdarts = [(i, j, cols[s]) for i, j, s in darts]
    return _unreached(k, G, D, pdarts) + dup * _PEN * G


def _anneal(d, D, k, G, cols, rng, deadline):
    """Simulated annealing over layer permutations and voltages. Returns (n, edges) or None."""
    P = [rng.sample(range(k), k) for _ in range(d)]
    V = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]

    def darts_of():
        return [(i, P[L][i], V[L][i]) for L in range(d) for i in range(k)]

    cost = _cost(k, G, D, darts_of(), cols)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        temp = 2.0 * (1.0 - (now - start) / span) + 0.15
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.7:
            i = rng.randrange(k)
            old = V[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            V[L][i] = new
            c2 = _cost(k, G, D, darts_of(), cols)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                V[L][i] = old
        else:
            a, b = rng.sample(range(k), 2)
            P[L][a], P[L][b] = P[L][b], P[L][a]
            c2 = _cost(k, G, D, darts_of(), cols)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                P[L][a], P[L][b] = P[L][b], P[L][a]

    if cost != 0:
        return None
    E = set()
    for L in range(d):
        for i in range(k):
            j = P[L][i]
            p = cols[V[L][i]].tolist()
            for x in range(G):
                E.add((i * G + x, (k + j) * G + p[x]))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break

    # Main search: aim above the current best order.
    ks = (1, 2, 2, 3, 3, 4)
    slice_len = max(2.0, budget / 6.0)
    try:
        while best[0] < moore and time.monotonic() < deadline - 0.5:
            need = best[0] // 2 + 1  # need k*G >= need so that 2kG > best order
            k = rng.choice(ks)
            G = -(-need // k) + rng.randrange(3)
            if 2 * k * G > moore:
                continue
            groups = _groups(G)
            if not groups:
                continue
            m, k2, r = rng.choice(groups)
            order, cols = _group_cols(m, k2, r)
            t_end = min(deadline, time.monotonic() + slice_len)
            res = _anneal(d, D, k, order, cols, rng, t_end)
            if res is not None:
                consider(*res)
    except Exception:
        pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
