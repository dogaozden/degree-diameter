import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Family 1 (D = 3 only): projective plane incidence and Araujo-Pardo-Lopez.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power in [3, 23]."""
    q = d - 2
    if 3 <= q <= 23 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
    return None


# ----------------------------------------------------------------------------
# Family 2 (new, main search): Haar graphs H(Z_m, S) with |S| = d.
#
# Vertices a_i = i and b_j = m + j; a_i ~ b_{i+s} for s in S.
# Translation i -> i + t and the swap a_i <-> b_{-i} are automorphisms, so every
# vertex pair is equivalent to a pair (a_0, z). Hence the diameter is at most D
# iff every vertex lies within distance D of a_0. One BFS from a_0 gives an exact
# cost: the number of vertices not reached within D steps (0 means valid).
# ----------------------------------------------------------------------------

def _haar_unreached(m, S, D):
    """Number of vertices of H(Z_m, S) at distance > D from a_0 (0 means diameter <= D)."""
    sa = bytearray(m)
    sb = bytearray(m)
    sa[0] = 1
    frontier = [0]
    on_a = True
    count = 1
    total = 2 * m
    for _ in range(D):
        new = []
        if on_a:
            for i in frontier:
                for s in S:
                    j = i + s
                    if j >= m:
                        j -= m
                    if not sb[j]:
                        sb[j] = 1
                        new.append(j)
        else:
            for j in frontier:
                for s in S:
                    i = j - s
                    if i < 0:
                        i += m
                    if not sa[i]:
                        sa[i] = 1
                        new.append(i)
        count += len(new)
        if count == total or not new:
            break
        frontier = new
        on_a = not on_a
    return total - count


def _search_m(d, D, m, rng, deadline):
    """Simulated annealing over S (|S| = d, 0 in S) in Z_m. Returns S or None."""
    if d < 2 or m < d:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    c = _haar_unreached(m, S, D)
    if c == 0:
        return S
    T = 2.0
    it = 0
    while True:
        it += 1
        if (it & 31) == 0 and time.monotonic() >= deadline:
            return None
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _haar_unreached(m, S, D)
        if c2 == 0:
            return S
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            S[i] = old
        T = max(0.3, T * 0.9995)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.75 * time_limit - 1.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        for builder in (_best_pg, _araujo):
            try:
                cand = builder(d)
            except Exception:
                cand = None
            if cand is not None:
                consider(cand[0], cand[1])

    if d >= 2 and D >= 2:
        rng = random.Random(seed * 1000003 + d * 31 + D)
        m = max(d, best_n // 2 + 1)
        while True:
            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0.05:
                break
            per = max(0.2, min(4.0, remaining / 6.0))
            end = min(deadline, now + per)
            S = _search_m(d, D, m, rng, end)
            if S is not None:
                n, e = lib.haar_graph(m, S)
                consider(n, e)
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
