import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baseline: incidence graph of PG(2, q) (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: abelian bi-Cayley (Haar-type) graphs over G = Z_m1 x Z_m2.
#
# Vertices A_g = g and B_g = h + g for g in G (|G| = h). Connection set S of
# d distinct group elements; A_g ~ B_{g+s} for s in S. This is d-regular and
# bipartite. Let D = S - S (contains 0). Then:
#   * A-to-A distance <= 2T_A  iff  D^(T_A) = G   (T_A = D//2 copies of D),
#   * A-to-B distance <= 2T_B+1 iff S + D^(T_B) = G   (T_B = (D-1)//2),
# where the diameter target is D. Searching S by simulated annealing on the
# uncovered counts replaces the layer/voltage search of the previous version.
# ----------------------------------------------------------------------------

def _divisors(h):
    return [m for m in range(1, h + 1) if h % m == 0]


def _tables(h, m1):
    """Addition and negation tables for Z_m1 x Z_m2 (m2 = h // m1), element a*m2 + b."""
    m2 = h // m1
    x = np.arange(h, dtype=np.int64)
    A = x // m2
    Bc = x % m2
    add = ((A[:, None] + A[None, :]) % m1) * m2 + (Bc[:, None] + Bc[None, :]) % m2
    neg = ((-A) % m1) * m2 + (-Bc) % m2
    return add.astype(np.int64), neg.astype(np.int64)


def _sumset(add, X, Y, h):
    """Indices of the sumset X + Y as a sorted int64 array."""
    cov = np.zeros(h, dtype=bool)
    cov[add[np.ix_(X, Y)].ravel()] = True
    return np.flatnonzero(cov)


def _cost(add, neg, S, h, TA, TB):
    """Number of uncovered elements for the A-A and A-B conditions."""
    D = _sumset(add, S, neg[S], h)          # S - S, contains 0
    DA = D
    for _ in range(TA - 1):
        DA = _sumset(add, DA, D, h)
    DB = D
    for _ in range(TB - 1):
        DB = _sumset(add, DB, D, h)
    SB = _sumset(add, S, DB, h)
    return (h - len(DA)) + (h - len(SB))


def _anneal(add, neg, h, d, TA, TB, rng, deadline, iters):
    """Simulated annealing over d-subsets of G. Returns the list S or None."""
    Sl = rng.sample(range(h), d)
    cost = _cost(add, neg, np.array(Sl, dtype=np.int64), h, TA, TB)
    for t in range(iters):
        if cost == 0:
            break
        if t % 256 == 0 and time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - t / iters) + 0.05
        j = rng.randrange(d)
        new = rng.randrange(h)
        if new in Sl:
            continue
        old = Sl[j]
        Sl[j] = new
        c2 = _cost(add, neg, np.array(Sl, dtype=np.int64), h, TA, TB)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            Sl[j] = old
    return Sl if cost == 0 else None


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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D < 3:
        return best

    # Main search: abelian bi-Cayley graphs, growing the group order h.
    TA = D // 2
    TB = (D - 1) // 2

    lo = max(d, best_n // 2)   # a feasible order (K_{d,d} or the PG graph)
    step = max(1, lo // 10)
    cur = lo + step
    fails = 0

    while time.monotonic() < deadline:
        h = cur
        if h < d:
            cur = lo + 1
            continue
        m1 = rng.choice(_divisors(h))
        add, neg = _tables(h, m1)
        slice_end = min(deadline, time.monotonic() + 4.0)
        Sl = _anneal(add, neg, h, d, TA, TB, rng, slice_end, 20000)
        if Sl is not None:
            Sa = np.array(Sl, dtype=np.int64)
            edges = [(g, h + int(add[g, s])) for g in range(h) for s in Sl]
            consider(2 * h, edges)
            lo = cur
            step = max(1, step * 2)
            cur = lo + step
            fails = 0
        else:
            fails += 1
            if fails >= 2:
                if step > 1:
                    step = max(1, step // 2)
                fails = 0
            cur = lo + step

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
