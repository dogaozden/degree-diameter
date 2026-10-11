import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# D = 3 and D = 4 structured baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW: vectorised bi-Cayley evaluator.
#
# A bi-Cayley graph over a group G of order N has A_x ~ B_{x g} for g in S.
# Each right multiplication by g is a permutation of G, stored as a row of the
# table RG (RG[g][x] = x*g). One BFS level from a whole frontier then becomes
# d boolean scatter-ORs with fancy indexing, instead of a Python loop over
# every vertex and edge. Only two sources (A_0 and B_0) need checking, because
# left multiplication is an automorphism that is transitive on each side.
# ----------------------------------------------------------------------------

MAX_GROUPS = 12
CLIMB_ITERS = 1200
_TABLE_CACHE = {}


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


def _group_arrays(m, k, r):
    """Cached (order, RG, invs): RG[g, x] = x*g as an int64 table, invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    RG = np.empty((order, order), dtype=np.int64)
    for g in range(order):
        RG[g] = [mul(x, g) for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, RG, invs)
    if len(_TABLE_CACHE) >= 32:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, RG, S, Sinv, D):
    """Number of ordered pairs (source, target) at distance > D, sources A_0 and B_0."""
    full = 2 * N
    total = 0
    for side in (0, 1):
        VA = np.zeros(N, dtype=bool)
        VB = np.zeros(N, dtype=bool)
        FA = np.zeros(N, dtype=bool)
        FB = np.zeros(N, dtype=bool)
        if side == 0:
            VA[0] = True
            FA[0] = True
        else:
            VB[0] = True
            FB[0] = True
        for _ in range(D):
            nB = np.zeros(N, dtype=bool)
            for g in S:
                nB[RG[g]] |= FA
            nA = np.zeros(N, dtype=bool)
            for h in Sinv:
                nA[RG[h]] |= FB
            nB &= ~VB
            nA &= ~VA
            if not nA.any() and not nB.any():
                break
            VB |= nB
            VA |= nA
            FA, FB = nA, nB
        total += full - int(VA.sum()) - int(VB.sum())
    return total


def _climb(N, RG, invs, d, D, rng, iters, deadline):
    """Annealing over a connection set S containing the identity (WLOG)."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, RG, S, [invs[g] for g in S], D)
    best_S, best_v = S, cur
    T0 = 4.0 + 0.05 * cur
    for step in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.2
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, RG, S2, [invs[g] for g in S2], D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best_v:
                best_S, best_v = S, cur
    return best_S if best_v == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: diameter 2, always valid.
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
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d >= 2 and best[0] < moore:
        tried = {}
        try:
            while best[0] < moore and time.monotonic() < deadline:
                n_best = best[0]
                lo = n_best // 2 + 1
                if lo > moore // 2:
                    break
                hi = min(moore // 2, lo + max(4, lo // 15))
                N = min(range(lo, hi + 1),
                        key=lambda x: (tried.get(x, 0), rng.random()))
                tried[N] = tried.get(N, 0) + 1
                if N < d:
                    continue
                groups = _groups(N)
                rng.shuffle(groups)
                found = None
                for m, k2, r in groups[:MAX_GROUPS]:
                    if time.monotonic() > deadline:
                        break
                    _, RG, invs = _group_arrays(m, k2, r)
                    S = _climb(N, RG, invs, d, D, rng, CLIMB_ITERS, deadline)
                    if S is not None:
                        found = (RG, S)
                        break
                if found is not None:
                    RG, S = found
                    edges = [(x, N + int(RG[g, x])) for x in range(N) for g in S]
                    consider(2 * N, edges)
        except Exception:
            pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
