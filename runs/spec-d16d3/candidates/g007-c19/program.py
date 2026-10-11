import random
import time

import lib


def _unreached(m, S, D, src):
    """Vertices not within distance D of src in the Haar graph H(m, S).

    a-vertex i is index i, b-vertex j is index m+j. a_i ~ b_{i+s}, b_j ~ a_{j-s}.
    """
    N = 2 * m
    seen = bytearray(N)
    seen[src] = 1
    frontier = [src]
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


def _cost(m, S, D):
    """Zero iff the Haar graph H(m, S) has diameter <= D.

    The graph is invariant under simultaneous translation of both sides, so the
    distances from a_0 and b_0 determine all pairwise distances.
    """
    c = _unreached(m, S, D, 0)
    if c:
        return c
    return c + _unreached(m, S, D, m)


def _haar_search(m, d, D, rng, deadline, iters):
    """Hill-climb a connection set S of size d containing 0 in Z_m so H(m, S) has diameter <= D."""
    if m < d or d < 1:
        return None
    if d == 1:
        S = [0]
        return S if _cost(m, S, D) == 0 else None
    others = list(range(1, m))
    S = [0] + rng.sample(others, d - 1)
    c = _cost(m, S, D)
    for it in range(iters):
        if c == 0:
            return S
        if (it & 15) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        ct = _cost(m, T, D)
        if ct <= c or rng.random() < 0.02:
            S, c = T, ct
    return S if c == 0 else None


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main family: cyclic Haar graphs H(m, S) with |S| = d, searched over m.
    # Order is 2m. Descending candidates m, with budgets doubling each round.
    moore = lib._moore_bound(d, D)
    hi = min(moore // 2, 400)
    lo = max(d + 1, best_n // 2 + 1)
    budget = 150
    while lo <= hi and time.monotonic() < deadline:
        m = hi
        progressed = False
        while m >= lo and time.monotonic() < deadline:
            S = _haar_search(m, d, D, rng, deadline, budget)
            if S is not None:
                n, e = lib.haar_graph(m, S)
                before = best_n
                consider(n, e)
                if best_n > before:
                    lo = m + 1
                    progressed = True
                    break
            m -= 1
        budget *= 2
        if not progressed and budget > 20000:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
