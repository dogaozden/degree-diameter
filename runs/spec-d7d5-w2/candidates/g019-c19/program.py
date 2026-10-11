import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baseline: incidence graph of PG(2, q), used for D = 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: Haar graphs H(m, S) over the cyclic group Z_m.
#
# Vertices a_i (i in Z_m) and b_j (j in Z_m); a_i ~ b_{i+s} for s in S, |S| = d.
# The graph is bipartite and d-regular with 2m vertices.
#
# Symmetry: translation x -> x + t, and the side swap a_i <-> b_{-i}, are
# automorphisms. So the diameter is at most D exactly when every vertex is within
# distance D of a_0. We fix 0 in S (translating S is an isomorphism).
#
# Search: hill climbing / annealing over the d-1 free shifts, minimising the
# number of vertices not reached from a_0 within D steps. A BFS over numpy
# boolean arrays costs O(D * d) rolls, so many thousands of candidates can be
# tested per second. Each success is checked with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _haar_cost(m, S, D):
    """Number of vertices NOT within distance D of a_0 in H(m, S)."""
    visA = np.zeros(m, dtype=bool)
    visB = np.zeros(m, dtype=bool)
    visA[0] = True
    front = visA.copy()
    side = 0  # 0: frontier lies on the A side, 1: on the B side
    for _ in range(D):
        new = np.zeros(m, dtype=bool)
        if side == 0:
            for s in S:
                new |= np.roll(front, s)  # a_i -> b_{i+s}
            new &= ~visB
            visB |= new
        else:
            for s in S:
                new |= np.roll(front, -s)  # b_j -> a_{j-s}
            new &= ~visA
            visA |= new
        front = new
        side ^= 1
        if not front.any():
            break
    return 2 * m - int(visA.sum()) - int(visB.sum())


def _climb(m, d, D, rng, deadline, iters):
    """Search for a shift set S (size d, containing 0) with H(m, S) of diameter <= D. Returns S or None."""
    if d > m:
        return None
    if d < 2:
        S = [0]
        return S if _haar_cost(m, S, D) == 0 else None
    S = [0] + rng.sample(range(1, m), d - 1)
    cur = _haar_cost(m, S, D)
    for t in range(iters):
        if cur == 0:
            return S
        if (t & 63) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        new = rng.randrange(m)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _haar_cost(m, S, D)
        temp = max(0.3, 2.0 * (1.0 - t / iters))
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            S[i] = old
    return S if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact construction for D = 3 (instant return when d - 1 is a prime power).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Main search: grow the Haar-graph order m while hill climbing succeeds.
    if d >= 2:
        bm = best_n // 2
        moore = lib.moore_bound(d, D)
        step = max(1, bm // 10)
        while time.monotonic() < deadline and step >= 1:
            m = bm + step
            if 2 * m > moore:
                step //= 2
                continue
            S = _climb(m, d, D, rng, deadline, 20000)
            if S is not None:
                n, e = lib.haar_graph(m, S)
                if n > best_n and lib.is_valid(n, e, d, D):
                    best = (n, e)
                    best_n = n
                    bm = m
                else:
                    step //= 2
            else:
                step //= 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
