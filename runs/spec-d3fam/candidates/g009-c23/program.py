import math
import random
import time

import lib


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _tiny(d, D):
    """A trivially valid graph used as the last resort."""
    if d >= 1 and D >= 1:
        return 2, [(0, 1)]
    return 1, []


def _cover_cost(S, m):
    """Number of nonzero residues x in Z_m that are NOT a difference s - t of two distinct elements of S."""
    seen = [False] * m
    for s in S:
        for t in S:
            if s != t:
                seen[(s - t) % m] = True
    return sum(1 for x in range(1, m) if not seen[x])


def _search_cover(m, d, rng, end):
    """Find S subset of Z_m, |S| = d, 0 in S, with S - S = Z_m (cyclic Haar graph of diameter 3).

    Simulated annealing on the number of uncovered differences, with random restarts.
    Returns S as a list, or None if the deadline `end` passes first.
    """
    if d < 2 or m < d:
        return None
    iters = 40000
    while time.monotonic() < end:
        S = [0] + rng.sample(range(1, m), d - 1)
        c = _cover_cost(S, m)
        for it in range(iters):
            if c == 0:
                return S
            if (it & 255) == 0 and time.monotonic() >= end:
                return None
            T = 1.0 * (0.1 ** (it / iters))
            i = rng.randrange(1, d)
            x = rng.randrange(1, m)
            if x in S:
                continue
            S2 = S[:]
            S2[i] = x
            c2 = _cover_cost(S2, m)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                S, c = S2, c2
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    # Structured bases (verified before use).
    best = None
    q = d - 1
    base = None
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        base = lib.projective_plane_incidence(q)
    elif D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        base = lib.araujo_lopez_graph(d - 2)
    if base is not None and lib.is_valid(base[0], base[1], d, D):
        best = base

    if D == 3 and d >= 2:
        # New construction: cyclic Haar graph H(Z_m, S) with |S| = d and S - S = Z_m.
        # Such a graph has order 2m, max degree d and diameter 3.
        # Search for S at increasing m, starting just above the current best.
        if best is None:
            cand = lib.haar_graph(d, range(d))
            if lib.is_valid(cand[0], cand[1], d, D):
                best = cand
        if best is None:
            best = _tiny(d, D)
        mmax = d * d - d + 1  # Moore bound for D = 3 is 2m with m = d^2 - d + 1
        m = best[0] // 2 + 1
        while m <= mmax and time.monotonic() < deadline:
            now = time.monotonic()
            rem = deadline - now
            end = min(deadline, now + max(1.0, 0.5 * rem))
            S = _search_cover(m, d, rng, end)
            if S is None:
                break
            n2, e2 = lib.haar_graph(m, S)
            if lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
                m += 1
            else:
                break
        if not lib.is_valid(best[0], best[1], d, D):
            best = _tiny(d, D)
        return best

    # General fallback for other cases: random Haar graphs.
    if best is None:
        cand = lib.haar_graph(d, range(d)) if d >= 1 else (1, [])
        best = cand if lib.is_valid(cand[0], cand[1], d, D) else _tiny(d, D)

    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10 and d >= 2:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found and lib.is_valid(found[0], found[1], d, D):
            if found[0] > best[0]:
                best = found
            misses = 0
        else:
            misses += 1
        m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = _tiny(d, D)
    return best
