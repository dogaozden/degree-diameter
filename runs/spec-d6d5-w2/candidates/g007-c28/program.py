import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Family 1: cyclic Haar graphs H(Z_m, S), |S| = d.
#
# Vertices a_i = i and b_j = m + j. Edge a_i -- b_{i+s} for each s in S.
# The graph is d-regular and bipartite. The map a_i <-> b_{-i} is an
# automorphism, and so are translations within each side, so the diameter is
# at most D iff every vertex lies within distance D of a_0. That makes the
# cost one BFS, which is cheap enough for hill-climbing over S.
# ----------------------------------------------------------------------------

def _haar_uncovered(m, S, D):
    """Number of the 2m vertices at distance > D from a_0 in H(Z_m, S). Zero means diameter <= D."""
    N = 2 * m
    seen = bytearray(N)
    seen[0] = 1
    frontier = [0]
    count = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < m:
                for s in S:
                    v = m + (u + s) % m
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                j = u - m
                for s in S:
                    v = (j - s) % m
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        count += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return N - count


def _haar_search(m, d, D, rng, deadline):
    """Anneal a connection set S (0 in S, |S| = d) in Z_m so H(Z_m, S) has diameter <= D."""
    if m < d or m < 2 or d < 2:
        return None
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    S = [0] + rng.sample(others, d - 1)
    c = _haar_uncovered(m, S, D)
    best_c = c
    stall = 0
    T = 1.0
    while c > 0:
        if time.monotonic() >= deadline:
            break
        if stall > 4000:
            # Restart from a fresh random set.
            S = [0] + rng.sample(others, d - 1)
            c = _haar_uncovered(m, S, D)
            best_c = c
            stall = 0
            T = 1.0
            continue
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        T2 = S[:]
        T2[i] = x
        c2 = _haar_uncovered(m, T2, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = T2, c2
        if c < best_c:
            best_c = c
            stall = 0
        else:
            stall += 1
        T = max(0.2, T * 0.999)
    return S if c == 0 else None


# ----------------------------------------------------------------------------
# Family 2: incidence graph of PG(2, d-1) when d-1 is a prime power and D >= 3.
# ----------------------------------------------------------------------------

def _pg_for(d):
    q = d - 1
    if q < 2 or q > 32 or not lib.is_prime_power(q):
        return None
    return lib.projective_plane_incidence(q)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3 and d >= 3:
        pg = _pg_for(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: cyclic Haar graphs with m increasing from just above the
    # current best. Each success raises the target by one.
    m = max(d + 1, best_n // 2 + 1)
    while time.monotonic() < deadline and 2 * m <= moore:
        now = time.monotonic()
        remaining = deadline - now
        budget = min(remaining, max(3.0, remaining * 0.2))
        S = _haar_search(m, d, D, rng, now + budget)
        if S is not None:
            n, e = lib.haar_graph(m, S)
            consider(n, e)
        m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
