"""Abelian multi-base voltage lifts searched by bitset annealing.

Construction: a bipartite graph with k base vertices per side and cyclic group Z_m.
Each layer L is a permutation p_L of range(k), giving darts (i, p_L[i], s) so that
every base vertex has exactly d darts. The lift has 2*k*m vertices, A_{i,x} ~ B_{j,x+s}.
Translations x -> x + c are automorphisms, so validity only needs BFS from the
2k sources A_{i,0} and B_{i,0}. Balls are stored as m-bit Python ints and advanced
with cyclic rotations, so each candidate is evaluated in microseconds.
Annealing minimises the number of unreached (source, vertex) pairs. Zero means valid.
Every result is re-checked with lib.is_valid before it is accepted.
"""
import math
import random
import time

import lib

_BIG = 10 ** 9
ANNEAL_T0 = 3.0
ANNEAL_T1 = 0.05


def _rot(X, s, m, mask):
    """Return the bitmask {x + s mod m : x in X}."""
    s %= m
    if s == 0:
        return X
    return ((X << s) | (X >> (m - s))) & mask


def _cost(k, m, D, darts, mask, limit):
    """Count (source, vertex) pairs not within distance D. Returns 0 iff the lift is valid.

    Stops early once the running total exceeds `limit`; the partial total is then returned.
    """
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    rots = [(i, j, s, (-s) % m) for i, j, s in darts]
    total = 0
    for i0 in range(k):
        for side in (0, 1):
            A = [0] * k
            B = [0] * k
            if side == 0:
                A[i0] = 1
            else:
                B[i0] = 1
            for _ in range(D):
                nA = list(A)
                nB = list(B)
                for i, j, s, ns in rots:
                    nB[j] |= _rot(A[i], s, m, mask)
                    nA[i] |= _rot(B[j], ns, m, mask)
                A, B = nA, nB
            total += sum(m - x.bit_count() for x in A)
            total += sum(m - x.bit_count() for x in B)
            if total > limit:
                return total
    return total


def _edges(k, m, darts):
    """Expand the darts into the explicit edge list of the 2*k*m-vertex lift."""
    E = []
    for i, j, s in darts:
        for x in range(m):
            E.append((i * m + x, (k + j) * m + (x + s) % m))
    return 2 * k * m, E


def _anneal(k, m, d, D, rng, deadline):
    """Time-scheduled simulated annealing over darts. Returns (n, edges) or None."""
    mask = (1 << m) - 1
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(m)])
    cost = _cost(k, m, D, darts, mask, _BIG)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = ANNEAL_T0
    it = 0
    while cost > 0:
        it += 1
        if (it & 31) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = min(1.0, (now - t0) / span)
            T = ANNEAL_T0 * (ANNEAL_T1 / ANNEAL_T0) ** frac
        u = 1.0 - rng.random()          # in (0, 1]
        thr = cost - T * math.log(u)    # Metropolis threshold; accept iff c2 <= thr
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            if rng.random() < 0.5:
                new = (old + rng.randint(-3, 3)) % m
            else:
                new = rng.randrange(m)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, m, D, darts, mask, thr)
            if c2 <= thr:
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, m, D, darts, mask, thr)
            if c2 <= thr:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return _edges(k, m, darts)
    return None


def _best_pg(d):
    """PG(2, q) incidence for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    q = next((q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)), None)
    if q is None:
        return None
    return lib.projective_plane_incidence(q)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 17 * d + 31 * D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: C_{2D} for d = 2 (Moore-optimal), K_{d,d} otherwise (diameter 2).
    if d == 2:
        n0 = 2 * D
        best = (n0, [(i, (i + 1) % n0) for i in range(n0)])
    else:
        best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baseline for D = 3 (projective plane).
    if D == 3 and d >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: abelian multi-base voltage lifts, aiming above the current best.
    if D >= 3 and d >= 3:
        slice_len = max(0.5, 0.06 * budget)
        while best[0] < moore and time.monotonic() < deadline:
            lo = best[0] // 2 + 1          # lower bound on m for k = 1
            if 2 * lo > moore:
                break
            k = rng.choice((1, 2, 2, 3, 3, 4))
            lo = best[0] // (2 * k) + 1
            if 2 * k * lo > moore:
                continue
            m = max(lo, lo + rng.randint(-2, 4))
            if 2 * k * m > moore:
                m = max(lo, moore // (2 * k))
                if 2 * k * m > moore:
                    continue
            sub_deadline = min(deadline, time.monotonic() + slice_len)
            res = _anneal(k, m, d, D, rng, sub_deadline)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
