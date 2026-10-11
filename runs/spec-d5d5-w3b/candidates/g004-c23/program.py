import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

ANNEAL_ITERS = 3000     # annealing steps per (group, connection set) attempt
_TABLE_CACHE = {}
_TABLE_CAP = 8          # group tables are N x N, keep the cache small


# ----------------------------------------------------------------------------
# Fallbacks that are valid for every (d, D).
# ----------------------------------------------------------------------------

def _fallback(d, D):
    """A small, certainly valid graph for the given (d, D)."""
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2 or d >= 3:
        # K_{d,d}: diameter 2, degree d, bipartite.
        return lib.haar_graph(d, range(d))
    # d == 2, D >= 3: even cycle C_{2D} has diameter D.
    n = 2 * D
    return n, [(i, (i + 1) % n) for i in range(n)]


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k, searched with a vectorised reachability
# count and simulated annealing on the connection set.
#
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism, so the pairs unreached from A_0 and
# B_0 decide the diameter. The identity is kept in S WLOG.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(m, k, r):
    """Cached (Tc, invs): Tc[g][x] = x*g as an int array, invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = np.array([[mul(x, g) for g in range(order)] for x in range(order)],
                 dtype=np.int64)
    Tc = np.ascontiguousarray(T.T)
    invs = [inv(g) for g in range(order)]
    val = (Tc, invs)
    if len(_TABLE_CACHE) >= _TABLE_CAP:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, Tc, invs, S, D):
    """Count (source, vertex) pairs not within distance D, sources A_0 and B_0.

    Each BFS layer is computed with boolean numpy arrays. Since x -> x*g is a
    bijection for fixed g, the fancy-indexed OR updates have no collisions.
    """
    colsS = [Tc[g] for g in S]
    colsI = [Tc[invs[g]] for g in S]   # B-to-A step: y -> y * g^-1
    total = 0
    for side in (0, 1):
        vA = np.zeros(N, dtype=bool)
        vB = np.zeros(N, dtype=bool)
        fA = np.zeros(N, dtype=bool)
        fB = np.zeros(N, dtype=bool)
        if side == 0:
            vA[0] = fA[0] = True
        else:
            vB[0] = fB[0] = True
        for _ in range(D):
            nB = np.zeros(N, dtype=bool)
            for c in colsS:
                nB[c] |= fA
            nA = np.zeros(N, dtype=bool)
            for c in colsI:
                nA[c] |= fB
            nB &= ~vB
            nA &= ~vA
            vB |= nB
            vA |= nA
            fA, fB = nA, nB
            if not (fA.any() or fB.any()):
                break
        total += 2 * N - int(vA.sum()) - int(vB.sum())
    return total


def _anneal(N, Tc, invs, d, D, rng, iters, deadline):
    """Anneal a connection set S (identity fixed in S) to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, Tc, invs, S, D)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, Tc, invs, S2, D)
        temp = 0.3 + 1.5 * (1.0 - it / iters)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _edges_from(N, Tc, S):
    """Edge list of the bi-Cayley graph: A_x -- B_{x g}, A-vertices 0..N-1."""
    E = []
    for g in S:
        col = Tc[g].tolist()
        E.extend((x, N + col[x]) for x in range(N))
    return 2 * N, E


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    best = _fallback(d, D)
    if d < 1 or D < 1:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baseline for D = 3.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Degree 1 or 2 is already optimal (or handled by the fallback).
    if d <= 2 or D <= 2:
        return best

    moore = lib.moore_bound(d, D)
    N = max(d, best[0] // 2 + 1)

    # Bi-Cayley search: for each order N try annealed connection sets over
    # several semidirect groups; on success move to the next order.
    while time.monotonic() < deadline and 2 * N <= moore:
        remaining = deadline - time.monotonic()
        quota = min(remaining, max(2.0, 0.15 * budget))
        qend = time.monotonic() + quota

        groups = _groups(N)
        if not groups:
            N += 1
            continue
        rng.shuffle(groups)

        found = None
        gi = 0
        while time.monotonic() < qend:
            m, k, r = groups[gi % len(groups)]
            gi += 1
            Tc, invs = _table(m, k, r)
            S = _anneal(N, Tc, invs, d, D, rng, ANNEAL_ITERS, qend)
            if S is not None:
                found = (Tc, S)
                break

        if found is not None:
            Tc, S = found
            n2, e2 = _edges_from(N, Tc, S)
            consider(n2, e2)
            N = max(N + 1, best[0] // 2 + 1)
        else:
            N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d, D)
    return best
