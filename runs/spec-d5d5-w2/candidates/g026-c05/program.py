import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

ANNEAL_ITERS = 4000     # annealing steps per candidate lift
SLICE_SECONDS = 3.0     # wall-clock cap per candidate lift
BIG = 10 ** 9           # cost for lifts with duplicate darts


# ----------------------------------------------------------------------------
# Baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products Z_m x|_r Z_k.
#
# Vertices: A_{i,g} and B_{j,g} for base indices i, j in range(k) and g in G.
# Each of the d layers is a perfect matching sigma_L on range(k); dart
# (i, sigma_L(i), s) joins A_{i,g} to B_{sigma_L(i), g*s} for all g.
# Left multiplication by G is an automorphism, so BFS from one representative
# per base vertex (2k sources) decides the diameter.
#
# Distance checks are done with numpy: the reached-set matrix R (2k x N) is
# expanded D times by a single dense matmul against the adjacency matrix.
# This is much faster than the pure-Python BFS and allows far more annealing.
# ----------------------------------------------------------------------------

def _groups(G):
    """Semidirect parameters (m, k, r) with m*k = G, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _perm_table(mul, G):
    """PERM[s, g] = g * s for the group with multiplication mul."""
    return np.array([[mul(g, s) for g in range(G)] for s in range(G)], dtype=np.int64)


def _assemble(k, G, darts, PERM):
    """Dense 0/1 adjacency matrix of the lift, A-vertices first, B-vertices after."""
    N = 2 * k * G
    A = np.zeros((N, N), dtype=np.float32)
    ar = np.arange(G, dtype=np.int64)
    for i, j, s in darts:
        rows = i * G + ar
        cols = (k + j) * G + PERM[s]
        A[rows, cols] = 1.0
        A[cols, rows] = 1.0
    return A


def _cost(k, G, D, darts, PERM):
    """Number of (representative, vertex) pairs not within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return BIG
    N = 2 * k * G
    A = _assemble(k, G, darts, PERM)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    r = len(reps)
    R = np.zeros((r, N), dtype=np.float32)
    R[np.arange(r), reps] = 1.0
    for _ in range(D):
        R = np.minimum(R + R @ A, 1.0)
    return int(r * N - round(float(R.sum())))


def _edges(k, G, darts, PERM):
    """Edge list of the lift as python int pairs."""
    E = set()
    ar = range(G)
    for i, j, s in darts:
        ps = PERM[s]
        for g in ar:
            E.add((i * G + g, (k + j) * G + int(ps[g])))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, PERM, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments. Returns darts or None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])

    cost = _cost(k, G, D, darts, PERM)
    T0 = 2.0 if cost >= BIG else 2.0 + 0.05 * cost
    T_end = 0.3
    ratio = T_end / T0

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (ratio ** (it / max(1, iters)))

        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            darts[idx][2] = new_s
            c2 = _cost(k, G, D, darts, PERM)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[idx][2] = old_s
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, PERM)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return darts
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(v, (v + 1) % n) for v in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: a different family from the parent's bi-Cayley annealing,
    # with numpy-accelerated cost evaluation over multi-base lifts.
    while best[0] < moore and time.monotonic() < deadline:
        target = best[0]
        if target + 1 > moore:
            break

        k = rng.choice((1, 2, 2, 3))
        lo = target // (2 * k) + 1
        if 2 * k * lo > moore:
            continue
        G = lo + rng.randrange(0, max(2, lo // 25))

        gl = _groups(G)
        if not gl:
            continue
        m, k2, r = rng.choice(gl)
        order, mul, _ = lib.semidirect_group(m, k2, r)
        PERM = _perm_table(mul, order)

        slice_end = min(deadline, time.monotonic() + SLICE_SECONDS)
        darts = _anneal(d, D, k, order, PERM, rng, slice_end, ANNEAL_ITERS)
        if darts is not None:
            n, e = _edges(k, order, darts, PERM)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
