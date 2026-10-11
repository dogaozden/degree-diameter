import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baselines (returned immediately when they are optimal).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bold change: cyclic bi-lifts with a larger base (k up to 8 blocks per side).
#
# The previous family used semidirect products Z_m x| Z_k2 with k <= 4. This
# version uses abelian Z_m only, but with base sizes k = 2..8. Each layer l is
# a perfect matching between A-blocks and B-blocks, realised as a bijection
# A_{i,g} -> B_{layers[l][i], g+s}. Every vertex then has degree d exactly.
#
# Reachability is tracked as a 2k-bit mask per vertex (bit b set when the
# representative vertex of block b is within distance D). Translation by Z_m
# is an automorphism, so the 2k representatives cover every orbit.
#
# Search: simulated annealing over voltages and block permutations, with
# defect-targeted voltage moves and restarts on stagnation. Sizes are chosen
# by a ladder: each trial aims just above the current best order.
#
# Safety: every candidate passes lib.is_valid before it replaces the best.
# The fallback is K_{d,d}, which is valid for any D >= 2.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _cyclic_search(d, D, k, m, rng, deadline, iters, patience):
    """Anneal a cyclic k-block bi-lift of order 2*k*m. Returns (n, edges) or None."""
    G = m
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    x = np.arange(G, dtype=np.int64)

    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)

    def setdart(l, i):
        j = layers[l][i]
        s = S[l][i]
        nbr[l, i * G:(i + 1) * G] = (k + j) * G + (x + s) % G
        nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + (x - s) % G

    for l in range(d):
        for i in range(k):
            setdart(l, i)

    def reach_of():
        r = np.zeros(N, dtype=np.int64)
        for b in range(2 * k):
            r[b * G] = 1 << b
        for _ in range(D):
            new = r.copy()
            for l in range(d):
                new |= r[nbr[l]]
            if np.array_equal(new, r):
                break
            r = new
        return r

    def cost_of(r):
        return 2 * k * N - int(_POP[r].sum())

    def dupcount():
        keys = {(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)}
        return d * k - len(keys)

    r = reach_of()
    cost = cost_of(r) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))

        if k >= 2 and rng.random() < 0.2:
            # Block-permutation move: swap the B-targets of two A-blocks in one layer.
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            setdart(l, i1)
            setdart(l, i2)
            r2 = reach_of()
            c2 = cost_of(r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, r = c2, r2
                if cost < best_cost:
                    best_cost, last = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                setdart(l, i1)
                setdart(l, i2)
            continue

        # Voltage move: defect-targeted with probability 0.5, otherwise uniform.
        l = None
        i = None
        if rng.random() < 0.5:
            bad = np.flatnonzero(r != full)
            if bad.size:
                v = int(bad[rng.randrange(bad.size)])
                block = v // G
                if block < k:
                    i = block
                    l = rng.randrange(d)
                else:
                    l = rng.randrange(d)
                    jj = block - k
                    if jj in layers[l]:
                        i = layers[l].index(jj)
        if i is None:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        setdart(l, i)
        r2 = reach_of()
        c2 = cost_of(r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, r = c2, r2
            if cost < best_cost:
                best_cost, last = cost, t
        else:
            S[l][i] = old
            setdart(l, i)

    if cost != 0:
        return None
    edges = set()
    for l in range(d):
        for u in range(N):
            v = int(nbr[l, u])
            edges.add((min(u, v), max(u, v)))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact construction: return immediately for the calibration case.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Ladder search: each trial aims just above the current best order.
    ks = list(range(2, 9))  # 2k <= 16 bits keeps the popcount table valid
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        m = best_n // (2 * k) + 1 + rng.randrange(0, 4)
        if m < 2:
            m = 2
        res = _cyclic_search(d, D, k, m, rng, deadline, 6000, 1500)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
