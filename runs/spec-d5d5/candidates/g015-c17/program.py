"""Cyclic bi-Cayley (Haar-type) lifts searched with bitset ball expansion.

A Haar graph H(m, S) has parts A_i, B_i (i in Z_m) with A_i ~ B_{i+s} for s in S.
Balls are stored as m-bit integers, so one expansion step is a few rotations and ORs.
Diameter is checked from A_0 and B_0 only, since Z_m translations act transitively
on each side. S is hill-climbed (with sideways moves and restarts) to zero unreached
pairs. Any Haar graph built here is checked with lib.is_valid before it is kept.
"""
import random
import time

import lib


def _rot(x, s, m, full):
    """Rotate the m-bit mask x so that bit i moves to bit (i + s) mod m."""
    if s == 0:
        return x
    return ((x << s) | (x >> (m - s))) & full


def _popc(x):
    return bin(x).count("1")


def _cost(m, S, NS, D, full):
    """Total number of (source, vertex) pairs not within distance D, sources A_0 and B_0.

    S holds the shifts; NS holds the negated shifts, used for B -> A steps.
    Zero means the Haar graph H(m, S) has diameter at most D.
    """
    total = 0
    for src_is_a in (True, False):
        SA = 1 if src_is_a else 0
        SB = 0 if src_is_a else 1
        for _ in range(D):
            nB = 0
            for s in S:
                nB |= _rot(SA, s, m, full)
            nA = 0
            for t in NS:
                nA |= _rot(SB, t, m, full)
            SA, SB = SA | nA, SB | nB
            if SA == full and SB == full:
                break
        total += (m - _popc(SA)) + (m - _popc(SB))
    return total


def _climb(m, d, D, rng, iters, deadline):
    """Hill-climb a shift set S of size d (containing 0, WLOG) to zero cost."""
    full = (1 << m) - 1
    S = [0] + rng.sample(range(1, m), d - 1)
    NS = [(-s) % m for s in S]
    cur = _cost(m, S, NS, D, full)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, m)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        NS2 = NS[:]
        NS2[i] = (-c) % m
        v = _cost(m, S2, NS2, D, full)
        if v <= cur:  # accept sideways moves to drift across plateaus
            S, NS, cur = S2, NS2, v
    return S if cur == 0 else None


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is always valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Structured baseline for D = 3.
    if D == 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: cyclic Haar lifts with 2m vertices, m just above the current best.
    if d >= 3 and best_n < moore:
        ITERS = 4000
        m0 = best_n // 2 + 1
        cands = list(range(m0, m0 + 40))
        attempt = 0
        while time.monotonic() < deadline and best_n < moore:
            if best_n // 2 + 1 != m0:
                m0 = best_n // 2 + 1
                cands = list(range(m0, m0 + 40))
                attempt = 0
            if m0 > moore // 2:
                break
            m = cands[attempt % len(cands)]
            attempt += 1
            if m < d or 2 * m > moore:
                continue
            S = _climb(m, d, D, rng, ITERS, deadline)
            if S is not None:
                edges = [(x, m + (x + s) % m) for x in range(m) for s in S]
                consider(2 * m, edges)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
