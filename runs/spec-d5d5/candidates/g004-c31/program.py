import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baseline for D = 3: incidence graph of PG(2, q), q the largest prime power
# with q + 1 <= d. It meets the Moore bound when d - 1 is a prime power.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New idea: a vectorized diameter oracle for bi-Cayley graphs.
#
# A bi-Cayley graph over a group G with connection set S has vertices A_x and
# B_y (x, y in G), with A_x ~ B_{x g} for g in S. Left translation is an
# automorphism that maps A_x -> A_{zx}, B_y -> B_{zy}, so both sides are
# vertex-transitive within their part. Hence the full diameter check reduces to
# two BFS runs, from A_0 and from B_0. Each BFS level is done with boolean
# numpy fancy-indexing over the group, which is roughly an order of magnitude
# faster than the list-based BFS.
#
# On top of this oracle, a simulated-annealing search over S (temperature
# schedule instead of plain hill-climbing, so it can cross plateaus) runs for
# every semidirect group of the current order, and the order N is swept
# upward from the smallest value that could beat the current best.
# ----------------------------------------------------------------------------

MAX_GROUPS = 6
ANNEAL_ITERS = 900
_CACHE = {}


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


def _tables(m, k, r):
    """Return (Tc, invs): Tc[g][x] = x*g as a numpy array, invs[g] = g^-1."""
    key = (m, k, r)
    hit = _CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    Tc = np.array([[mul(x, g) for x in range(order)] for g in range(order)],
                  dtype=np.int64)
    invs = [inv(g) for g in range(order)]
    val = (Tc, invs)
    if len(_CACHE) >= 64:
        _CACHE.clear()
    _CACHE[key] = val
    return val


def _unreached(N, Tc, invs, S, D):
    """Number of (source, vertex) pairs not within distance D, sources A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    total = 0
    for side in (0, 1):
        seenA = np.zeros(N, dtype=bool)
        seenB = np.zeros(N, dtype=bool)
        rA = np.zeros(N, dtype=bool)
        rB = np.zeros(N, dtype=bool)
        if side == 0:
            rA[0] = seenA[0] = True
        else:
            rB[0] = seenB[0] = True
        reached = 1
        for _ in range(D):
            nB = np.zeros(N, dtype=bool)
            nA = np.zeros(N, dtype=bool)
            for g in S:          # A_x -> B_{x g}
                nB[Tc[g]] |= rA
            for h in Sinv:       # B_z -> A_{z g^-1}
                nA[Tc[h]] |= rB
            nB &= ~seenB
            nA &= ~seenA
            seenB |= nB
            seenA |= nA
            c = int(nA.sum()) + int(nB.sum())
            reached += c
            rA, rB = nA, nB
            if c == 0:
                break
        total += 2 * N - reached
    return total


def _anneal_S(N, Tc, invs, d, D, rng, iters, deadline):
    """Anneal a connection set S (identity fixed WLOG) to zero unreached pairs."""
    if d < 2 or d > N:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, Tc, invs, S, D)
    temp = 2.0
    decay = (0.05 / 2.0) ** (1.0 / max(1, iters))
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            temp *= decay
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, Tc, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
        temp *= decay
    return S if cur == 0 else None


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

    # Safe fallback: K_{d,d} has diameter 2 and order 2d.
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

    # Sweep the bi-Cayley order N upward from the smallest N that beats the
    # current best (a lift on 2N vertices), trying several groups per N.
    N = best[0] // 2 + 1
    while best[0] < moore and 2 * N <= moore and time.monotonic() < deadline:
        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            Tc, invs = _tables(m, k, r)
            S = _anneal_S(N, Tc, invs, d, D, rng, ANNEAL_ITERS, deadline)
            if S is not None:
                found = (Tc, S)
                break
        if found is not None:
            Tc, S = found
            edges = [(x, N + int(Tc[g][x])) for x in range(N) for g in S]
            consider(2 * N, edges)
            N = max(N + 1, best[0] // 2 + 1)
        else:
            N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
