import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Projective plane incidence (exact record for D = 3 when d - 1 is a prime power).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bold change: cyclic Haar graphs searched directly for diameter D.
#
# Haar graph H(m, S): a_i ~ b_{i+s} for s in S, |S| = d, S containing 0 WLOG.
# It is bipartite and d-regular on 2m vertices. Translations act transitively
# on each side, so the diameter condition only needs BFS from a_0 and from b_0.
# The search is simulated annealing on S, with cost = number of (source, vertex)
# pairs not reached within D steps. Cost zero means diameter <= D. Growing m
# above the record is the goal.
# ----------------------------------------------------------------------------

def _haar_cost(m, S, D):
    """Unreached (source, vertex) pairs for sources a_0 and b_0 within D steps."""
    cost = 0
    for side in (0, 1):
        fa = np.zeros(m, dtype=bool)
        fb = np.zeros(m, dtype=bool)
        if side == 0:
            fa[0] = True
        else:
            fb[0] = True
        seen_a = fa.copy()
        seen_b = fb.copy()
        for _ in range(D):
            na = np.zeros(m, dtype=bool)
            nb = np.zeros(m, dtype=bool)
            for s in S:
                nb |= np.roll(fa, s)     # b_j <- a_{j-s}
                na |= np.roll(fb, -s)    # a_i <- b_{i+s}
            na &= ~seen_a
            nb &= ~seen_b
            seen_a |= na
            seen_b |= nb
            fa, fb = na, nb
            if not (fa.any() or fb.any()):
                break
        cost += 2 * m - int(seen_a.sum()) - int(seen_b.sum())
    return cost


def _search_haar(m, d, D, rng, deadline, iters):
    """Anneal a connection set S (|S| = d, 0 in S) in Z_m; return S with diameter <= D, or None."""
    if m < d + 1:
        return None
    others = list(range(1, m))
    S = [0] + rng.sample(others, d - 1)
    c = _haar_cost(m, S, D)
    T = 2.0
    for it in range(iters):
        if c == 0:
            return S
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(1, d)
        newv = rng.randrange(1, m)
        if newv in S:
            continue
        T2 = S[:]
        T2[i] = newv
        c2 = _haar_cost(m, T2, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = T2, c2
        T = max(0.3, T * 0.9995)
    return S if c == 0 else None


def _moore_half(d, D):
    """Half the Moore bound for bipartite graphs, i.e. the largest useful m for a Haar graph."""
    if d < 3:
        return max(d, 1) + D
    return sum((d - 1) ** i for i in range(D))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Calibration family: exact PG(2, q) incidence for D = 3.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main family: cyclic Haar graphs with annealed connection sets.
    if d >= 2 and time.monotonic() < deadline:
        half_moore = _moore_half(d, D)
        m = max(d + 1, int(0.66 * half_moore))
        found = None
        while m >= d + 1 and time.monotonic() < deadline:
            S = _search_haar(m, d, D, rng, deadline, iters=20000)
            if S is not None:
                found = (m, S)
                break
            m -= 2

        if found is not None:
            n, e = lib.haar_graph(found[0], found[1])
            consider(n, e)
            # Push m upward, with restarts, until the deadline.
            while time.monotonic() < deadline:
                m_try = found[0] + 1
                S = _search_haar(m_try, d, D, rng, deadline, iters=20000)
                if S is not None:
                    found = (m_try, S)
                    n, e = lib.haar_graph(m_try, S)
                    consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
