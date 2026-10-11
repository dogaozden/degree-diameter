import math
import random
import time

import numpy as np

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over Z_m x| Z_k2 with a fast numpy reachability cost.
#
# A lift has k A-orbits and k B-orbits, each of size G, so N = 2kG vertices.
# Layer L of the base graph is a permutation p_L of {0..k-1}, so each A-orbit
# has one dart into each B-orbit it hits and every vertex has degree d.
# Dart (i, j, s) joins (A, i, g) to (B, j, g*s). The group acts by left
# translation, so distances from one representative per orbit are enough.
# The cost is the number of (representative, vertex) pairs at distance > D.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G. Returns (order, mul table) or None."""
    for _ in range(60):
        divs = [x for x in range(1, min(G, 12) + 1) if G % x == 0]
        k2 = rng.choice(divs)
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in range(1, m)
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        order, mul, _ = lib.semidirect_group(m, k2, r)
        table = np.array([[mul(x, y) for y in range(order)] for x in range(order)],
                         dtype=np.int64)
        return order, table
    return None


def _cost(k, G, D, darts, MUL):
    """Unreached (representative, vertex) pairs within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    M = np.eye(N, dtype=np.float32)
    gidx = np.arange(G)
    for i, j, s in darts:
        a = i * G + gidx
        b = (k + j) * G + MUL[:, s]
        M[a, b] = 1.0
        M[b, a] = 1.0
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    R = np.zeros((len(reps), N), dtype=np.float32)
    R[np.arange(len(reps)), reps] = 1.0
    for _ in range(D):
        R = np.minimum(R @ M, 1.0)
        if np.count_nonzero(R) == R.size:
            break
    return int(R.size - np.count_nonzero(R))


def _edges(k, G, darts, MUL):
    E = set()
    for i, j, s in darts:
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + int(MUL[g, s])
            E.add((min(a, b), max(a, b)))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, MUL, rng, deadline, iters):
    """Simulated annealing over voltages and layer permutations. Returns darts or None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    # Make initial triples distinct when possible.
    for _ in range(200):
        if len({(i, j, s) for i, j, s in darts}) == len(darts):
            break
        for dart in darts:
            dart[2] = rng.randrange(G)

    cost = _cost(k, G, D, darts, MUL)
    T0, T1 = 2.0, 0.15
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters - 1))
        if rng.random() < 0.6 or k == 1:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, MUL)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, MUL)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    return darts if cost == 0 else None


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.75 * time_limit - 1.0)
    rng = random.Random(seed)

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

    if D == 2:
        return best

    # Projective plane incidence graph: diameter 3, degree q+1 <= d.
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            consider(*lib.projective_plane_incidence(q))
            break

    if D < 4:
        return best

    moore = lib._moore_bound(d, D)
    while time.monotonic() < deadline and best_n < moore:
        k = rng.choice([1, 2, 2, 3, 3, 4, 5, 6])
        span = moore - best_n
        if span < 1:
            break
        # Bias toward targets just above the current best.
        target = best_n + 1 + int(span * rng.random() ** 2)
        G = -(-target // (2 * k))
        if G < 2 or 2 * k * G > moore or G > 400:
            continue
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, MUL = g
        attempt_deadline = min(deadline, time.monotonic() + 8.0)
        darts = _anneal(d, D, k, order, MUL, rng, attempt_deadline, 4000)
        if darts is not None:
            n, e = _edges(k, order, darts, MUL)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
