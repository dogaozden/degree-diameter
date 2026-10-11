import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
ANNEAL_ITERS = 6000      # annealing steps per attempt
CHUNK_SECONDS = 8.0      # wall-clock slice per (k, group, order) attempt
MAX_K = 4                # fiber count per side for multi-base lifts
_PERM_CACHE = {}


# ----------------------------------------------------------------------------
# Baseline: projective plane incidence graph for D = 3 (exact when d-1 is a prime power).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: vectorised multi-base voltage lifts with annealed voltages.
#
# Base graph: k "A" vertices and k "B" vertices, with d layers. Layer L is a
# perfect matching between the A and B base vertices given by a permutation
# sig[L]; each matched pair carries a voltage volt[L][i] in a finite group G
# (semidirect product Z_m x| Z_k). Lifting gives a bipartite graph on 2kG
# vertices where every vertex has exactly one neighbour per layer, so the
# degree is exactly d. Vertex (i, g) of A-fibre i is joined to
# (j, g * s) in B-fibre j for each layer whose dart is (i -> j, s).
#
# Left multiplication is an automorphism, so the diameter check only needs
# one representative per base vertex. The check is done with numpy boolean
# reachability over all representatives at once, and simulated annealing
# minimises the number of unreached (representative, vertex) pairs.
# ----------------------------------------------------------------------------

def _groups(G):
    """Semidirect parameters (m, k, r) with m * k = G, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _perm_tables(G, mul, inv):
    """P[s][g] = g*s and Q[s][h] = h*s^-1, as int64 arrays (cached per group order/params)."""
    P = np.array([[mul(g, s) for g in range(G)] for s in range(G)], dtype=np.int64)
    Q = np.array([[mul(h, inv(s)) for h in range(G)] for s in range(G)], dtype=np.int64)
    return P, Q


def _get_tables(m, k, r):
    key = (m, k, r)
    hit = _PERM_CACHE.get(key)
    if hit is None:
        order, mul, inv = lib.semidirect_group(m, k, r)
        hit = (order, _perm_tables(order, mul, inv))
        if len(_PERM_CACHE) >= 32:
            _PERM_CACHE.clear()
        _PERM_CACHE[key] = hit
    return hit


def _build_nb(k, G, sig, volt, P, Q):
    """For each layer, the neighbour index of every lifted vertex (an involution per layer)."""
    N = 2 * k * G
    nbs = []
    for L in range(len(sig)):
        nb = np.empty(N, dtype=np.int64)
        for i in range(k):
            j = sig[L][i]
            s = volt[L][i]
            nb[i * G:(i + 1) * G] = (k + j) * G + P[s]
            nb[(k + j) * G:(k + j + 1) * G] = i * G + Q[s]
        nbs.append(nb)
    return nbs


def _cost(k, G, D, nbs, reps):
    """Number of (representative, vertex) pairs not within distance D. Zero means valid."""
    N = 2 * k * G
    R = np.zeros((len(reps), N), dtype=bool)
    R[np.arange(len(reps)), np.array(reps, dtype=np.int64)] = True
    for _ in range(D):
        new = R.copy()
        for nb in nbs:
            new |= R[:, nb]
        if np.array_equal(new, R):
            break
        R = new
    return len(reps) * N - int(R.sum())


def _edges(k, G, d, sig, volt, P):
    """Edge list of the lift, A-vertices first, B-vertices after."""
    E = set()
    for L in range(d):
        for i in range(k):
            j = sig[L][i]
            s = volt[L][i]
            for g in range(G):
                E.add((i * G + g, (k + j) * G + int(P[s][g])))
    return 2 * k * G, sorted(E)


def _anneal(k, G, d, D, P, Q, rng, deadline, iters):
    """Simulated annealing over per-layer matchings and voltages. Returns (sig, volt) or None."""
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    sig = [rng.sample(range(k), k) for _ in range(d)]
    volt = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]

    def evaluate(sg, vt):
        keys = {(i, sg[L][i], vt[L][i]) for L in range(d) for i in range(k)}
        if len(keys) < d * k:          # duplicate edge would appear
            return _BIG
        return _cost(k, G, D, _build_nb(k, G, sg, vt, P, Q), reps)

    cost = evaluate(sig, volt)
    T0, T1 = 2.0, 0.2
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = T0 * (T1 / T0) ** (it / max(1, iters))
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.6:
            i = rng.randrange(k)
            old = volt[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            volt[L][i] = new
            c2 = evaluate(sig, volt)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                volt[L][i] = old
        else:
            a, b = rng.sample(range(k), 2)
            sig[L][a], sig[L][b] = sig[L][b], sig[L][a]
            c2 = evaluate(sig, volt)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                sig[L][a], sig[L][b] = sig[L][b], sig[L][a]
    if cost == 0:
        return sig, volt
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for any d >= 1 and D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and n <= moore and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if best[0] >= moore:
            return best

    # Main search: multi-base voltage lifts, aiming strictly above the current best.
    while time.monotonic() < deadline and best[0] < moore:
        k = rng.randint(1, MAX_K)
        lo = best[0] // (2 * k) + 1
        G = lo + rng.randrange(max(2, lo // 15))
        if 2 * k * G > moore:
            G = moore // (2 * k)
            if G < 1:
                break
        groups = _groups(G)
        if not groups:
            continue
        m, kk, r = rng.choice(groups)
        order, (P, Q) = _get_tables(m, kk, r)

        remaining = deadline - time.monotonic()
        if remaining <= 0.05:
            break
        chunk = min(CHUNK_SECONDS, remaining)
        res = _anneal(k, order, d, D, P, Q, rng,
                      time.monotonic() + chunk, ANNEAL_ITERS)
        if res is not None:
            sig, volt = res
            n, e = _edges(k, order, d, sig, volt, P)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
