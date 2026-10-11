import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction family used by the search: cyclic Haar graphs.
#
# Haar graph H(m, S): parts a_x and b_y (x, y in Z_m), with a_x ~ b_{x+s} for s in S.
# It is bipartite and d-regular when |S| = d. The cyclic group acts transitively on
# each part, so diameter <= D only has to be checked from a_0 and b_0.
#
# This replaces the projective-plane arc extensions of the parent. The search is
# over the connection set S for a fixed m, with m swept upward from the current best.
# Each cost evaluation is a bitset BFS (rotations of m-bit integers), so many
# annealing steps fit in the budget.
# ----------------------------------------------------------------------------


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(min(d - 1, 60), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _rot(X, s, m, full):
    """Cyclic shift of an m-bit set: bit x moves to bit (x + s) mod m."""
    if s == 0:
        return X
    return ((X << s) | (X >> (m - s))) & full


def _unreached(m, S, negs, D, full, side):
    """Number of vertices not within distance D of the source (side, index 0)."""
    reached = [0, 0]
    reached[side] = 1
    frontier = 1
    cur = side
    for _ in range(D):
        shifts = S if cur == 0 else negs
        nxt = 0
        for s in shifts:
            nxt |= _rot(frontier, s, m, full)
        other = 1 - cur
        nxt &= ~reached[other]
        if not nxt:
            break
        reached[other] |= nxt
        frontier = nxt
        cur = other
    return 2 * m - reached[0].bit_count() - reached[1].bit_count()


def _cost(m, S, D, full):
    """Total unreached (source, vertex) pairs from a_0 and b_0. Zero means diameter <= D."""
    negs = [(-s) % m for s in S]
    return _unreached(m, S, negs, D, full, 0) + _unreached(m, S, negs, D, full, 1)


def _anneal_haar(m, d, D, deadline, rng):
    """Anneal a connection set S (|S| = d, 0 in S) in Z_m so that H(m, S) has diameter <= D."""
    full = (1 << m) - 1
    S = [0] + rng.sample(range(1, m), d - 1)
    inS = set(S)
    c = _cost(m, S, D, full)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while c > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = 1.5 * (1.0 - frac) + 0.05
        i = rng.randrange(1, d)
        new = rng.randrange(1, m)
        if new in inS:
            continue
        old = S[i]
        S[i] = new
        c2 = _cost(m, S, D, full)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
            inS.discard(old)
            inS.add(new)
        else:
            S[i] = old
    return list(S) if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = 0.8 * time_limit
    deadline = start + budget
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

    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Already at the Moore bound (e.g. calibration cases): nothing to search.
    moore = _moore(d, D)
    if best_n >= moore or d < 3:
        return best

    # Main search: Haar graphs over Z_m for increasing m, starting just above the current best.
    m = max(d, best_n // 2 + 1)
    m_max = moore // 2
    per_m = max(0.5, budget * 0.05)
    while m <= m_max and time.monotonic() < deadline:
        sub_deadline = min(deadline, time.monotonic() + per_m)
        S = _anneal_haar(m, d, D, sub_deadline, rng)
        if S is not None:
            n, e = lib.haar_graph(m, S)
            consider(n, e)
        m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
