import math
import random
import time

import lib


def _fallback(d, D):
    """A valid baseline: K_{d,d} (diameter 2) when D >= 2, otherwise a single edge."""
    if D >= 2:
        n, edges = lib.haar_graph(d, range(d))
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return 2, [(0, 1)]


def _groups_of_order(N, rng):
    """Candidate groups Z_m x|_r Z_k with m*k = N, as (m, k, r) triples.

    Non-abelian groups (k > 1, r != 1) come first. Abelian groups are poor for
    diameter, so they are only used after the non-abelian ones.
    """
    nonab, ab = [], []
    for m in range(2, N + 1):
        if N % m:
            continue
        k = N // m
        for r in range(1, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
                continue
            if k > 1 and r % m != 1:
                nonab.append((m, k, r))
            else:
                ab.append((m, k, r))
    rng.shuffle(nonab)
    rng.shuffle(ab)
    return nonab + ab


def _lift(N, mul, S):
    """Bipartite Haar-type group lift: part A = G, part B = G, x ~ x*g for g in S."""
    return lib.group_lift(2, [(0, 1, g) for g in S], N, mul)


def _score(N, mul, S, D):
    """Number of vertex pairs at distance more than D; zero means a valid diameter."""
    n, edges = _lift(N, mul, S)
    return lib.bad_pairs(n, edges, D)


def _climb(N, mul, d, D, rng, t_end, iters):
    """Local search over connection sets S (|S| = d) minimising bad pairs."""
    if d > N:
        return None
    S = rng.sample(range(N), d)
    cur = _score(N, mul, S, D)
    steps = 0
    while cur > 0 and steps < iters and time.monotonic() < t_end:
        steps += 1
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in S:
            continue
        T = list(S)
        T[i] = g
        sc = _score(N, mul, T, D)
        if sc <= cur or rng.random() < 0.02:
            S, cur = T, sc
    return S if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)
    best = _fallback(d, D)

    # Known optimal / record constructions for diameter 3, verified before use.
    if D == 3:
        q = d - 1
        if lib.is_prime_power(q):
            cand = lib.projective_plane_incidence(q)
            if lib.is_valid(cand[0], cand[1], d, D):
                return cand
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                cand = lib.araujo_lopez_graph(q)
                if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                    best = cand
            except Exception:
                pass

    # Search group-lifted Haar graphs over non-abelian groups of increasing order N.
    # Each group of order N gives a bipartite graph with 2N vertices.
    moore = lib.moore_bound(d, D)
    group_cache = {}
    N = max(d, 1)
    while time.monotonic() < deadline and 2 * N <= moore:
        if 2 * N > best[0]:
            if N not in group_cache:
                group_cache[N] = _groups_of_order(N, rng)
            t_end_N = min(deadline, time.monotonic() + 1.0)
            found = None
            for (m, k, r) in group_cache[N]:
                if time.monotonic() >= t_end_N:
                    break
                order, mul, _ = lib.semidirect_group(m, k, r)
                S = _climb(order, mul, d, D, rng, t_end_N, 300)
                if S is not None:
                    n, edges = _lift(order, mul, S)
                    if lib.is_valid(n, edges, d, D):
                        found = (n, edges)
                        break
            if found is not None:
                best = found
        N += 1

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return _fallback(d, D)
