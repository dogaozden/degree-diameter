"""Haar graphs over metacyclic groups, found by hill-climbing.

Phase 0: PG(2,q) incidence for D = 3 when d-1 is a prime power (optimal).
Phase 1: cyclic Haar search (the parent's method) for a safe baseline.
Phase 2: for a random group order N above the current best, pick a random
         metacyclic group Z_m x| Z_k of that order and hill-climb a connection
         set S of size d, minimising lib.bad_pairs for the Haar graph on G x {0,1}.
         Haar graphs are bipartite with degree d, so only the diameter must be
         searched. Every adopted graph passes lib.is_valid.
Fallback: K_{d,d}, which is valid for D >= 2.
"""
import math
import random
import time

import lib


def _haar_edges(N, mul, S):
    """Edges (x, N + x*s) for x in G and s in S; side 0 is 0..N-1, side 1 is N..2N-1."""
    return [(x, N + mul(x, s)) for x in range(N) for s in S]


def _metacyclic_params(N):
    """All (m, k, r) with m*k = N giving Z_m x| Z_k (r = 1 is a direct product)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _climb(N, mul, d, D, rng, steps, deadline):
    """Hill-climb a connection set S of size d in G; return S if the Haar graph has diameter <= D."""
    S = rng.sample(range(N), d)
    cur = lib.bad_pairs(2 * N, _haar_edges(N, mul, S), D)
    for _ in range(steps):
        if cur == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        c = lib.bad_pairs(2 * N, _haar_edges(N, mul, T), D)
        if c <= cur:  # accept plateau moves too
            S, cur = T, c
    return S if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    best_side = d

    # Phase 1: cyclic Haar search (cheap, safe baseline).
    cyc_deadline = start + 0.15 * time_limit
    m, misses = d + 1, 0
    while time.monotonic() < cyc_deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= cyc_deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            if found[0] > best[0] and lib.is_valid(found[0], found[1], d, D):
                best, best_side = found, m
            misses = 0
        else:
            misses += 1
        m += 1

    # Phase 2: random metacyclic groups, biased toward orders just above the best so far.
    hi = lib.moore_bound(d, D) // 2  # bipartite Haar side size cannot exceed Moore/2
    cache = {}
    while time.monotonic() < deadline:
        lo = best_side + 1
        if lo > hi:
            break
        N = lo + int((hi - lo) * rng.random() ** 2)
        if N not in cache:
            cache[N] = _metacyclic_params(N)
        if not cache[N]:
            continue
        m_, k_, r_ = rng.choice(cache[N])
        order, mul, _inv = lib.semidirect_group(m_, k_, r_)
        S = _climb(order, mul, d, D, rng, 300, deadline)
        if S is None:
            continue
        edges = _haar_edges(order, mul, S)
        if lib.is_valid(2 * order, edges, d, D):
            best, best_side = (2 * order, edges), order

    n, edges = best
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return lib.haar_graph(d, range(d))
