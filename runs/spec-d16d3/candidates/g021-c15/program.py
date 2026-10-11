import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cyclic Haar graphs H(Z_m, S) with |S| = d.
#
# Vertices a_x = x and b_y = m + y. a_x ~ b_{x+s} for s in S.
# The map a_x <-> b_{-x} is an automorphism, and translations act transitively
# on each side, so the diameter is at most D iff a_0 reaches every vertex
# within D steps. Frontiers are bitmasks over Z_m, so each cost evaluation is
# a handful of big-int shifts.
# ----------------------------------------------------------------------------

def _rot(mask, k, m, full):
    """Bit x of the result is bit (x - k) mod m of mask."""
    if k == 0:
        return mask
    return ((mask << k) | (mask >> (m - k))) & full


def _haar_cost(m, S, negS, D, full):
    """Number of vertices NOT within distance D of a_0 (0 means valid)."""
    visA = 1
    visB = 0
    fA = 1
    fB = 0
    for lvl in range(D):
        if lvl % 2 == 0:
            nb = 0
            for s in S:
                nb |= _rot(fA, s, m, full)
            nb &= ~visB & full
            visB |= nb
            fB = nb
        else:
            na = 0
            for s in negS:
                na |= _rot(fB, s, m, full)
            na &= ~visA & full
            visA |= na
            fA = na
    return (m - visA.bit_count()) + (m - visB.bit_count())


def _search_haar(m, d, D, rng, deadline):
    """Simulated annealing for S (|S| = d, 0 in S) with zero cost, or None."""
    full = (1 << m) - 1
    S = [0] + rng.sample(range(1, m), d - 1)
    c = _haar_cost(m, S, [(-s) % m for s in S], D, full)
    T = 1.0
    it = 0
    while True:
        if c == 0:
            return S
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _haar_cost(m, S, [(-s) % m for s in S], D, full)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            S[i] = old
        T = max(0.15, T * 0.999)
        if it % 3000 == 0:
            T = 1.0  # periodic reheating
    return S if c == 0 else None


# ----------------------------------------------------------------------------
# Baselines (always-valid fallbacks).
# ----------------------------------------------------------------------------

def _pg_baseline(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2), or C_{2D} when d = 2.
    if d == 2:
        n0 = 2 * D
        best = (n0, [(i, (i + 1) % n0) for i in range(n0)])
    else:
        best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])
        best_n = 2

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Projective plane incidence baseline (diameter 3).
    if D >= 3 and d >= 3:
        pg = _pg_baseline(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: Haar graphs over Z_m, ascending m.
    # Largest m allowed by the Moore-type counting bound (each a-vertex reaches
    # at most sum (d-1)^i vertices within i steps), capped for safety.
    if d >= 3:
        m_max = min(sum((d - 1) ** i for i in range(D)), 1200)
        fails = 0
        m = d
        while m <= m_max and time.monotonic() < deadline and fails < 8:
            dl = min(deadline, time.monotonic() + 3.0)
            S = _search_haar(m, d, D, rng, dl)
            if S is None:
                fails += 1
            else:
                fails = 0
                n, e = lib.haar_graph(m, S)
                consider(n, e)
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d)) if d >= 1 else (1, [])
    return best
