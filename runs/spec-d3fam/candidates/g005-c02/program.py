import math
import random
import time

import lib


def _ab_cost(m, S):
    """Cost of a candidate connection set S in Z_m.

    First term: nonzero residues not covered by S - S (needed for a-a and b-b distances <= 2).
    Once that is zero, second term: residues not covered by S + S - S, the walks of length 3
    that a-b distance 3 needs (distance-1 pairs are covered by S itself).
    """
    dif = set()
    for a in S:
        for b in S:
            if a != b:
                dif.add((a - b) % m)
    cost_d = (m - 1) - len(dif)
    if cost_d:
        return cost_d
    T = set(S)
    for x in S:
        for y in S:
            for z in S:
                T.add((x + y - z) % m)
    return m - len(T)


def _search_S(m, d, rng, deadline):
    """Simulated annealing for a d-element S (containing 0) in Z_m with cost 0, or None at deadline."""
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, m), d - 1)
        cost = _ab_cost(m, S)
        temp = 1.0
        for step in range(30000):
            if cost == 0:
                return S
            if step % 256 == 0 and time.monotonic() >= deadline:
                return None
            i = rng.randrange(1, d)
            x = rng.randrange(1, m)
            if x in S:
                continue
            old = S[i]
            S[i] = x
            new = _ab_cost(m, S)
            if new <= cost or rng.random() < math.exp((cost - new) / temp):
                cost = new
            else:
                S[i] = old
            temp = max(0.1, temp * 0.9997)
        if cost == 0:
            return S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    # Structured base (parent's construction), used as the safe fallback.
    base = None
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        base = lib.projective_plane_incidence(q)
    elif D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        base = lib.araujo_lopez_graph(d - 2)

    best = None
    if base is not None and lib.is_valid(base[0], base[1], d, D):
        best = base
    if best is None:
        best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid

    if D == 3:
        # Cyclic Haar graphs: order 2m, degree d, diameter 3 iff S-S and S+S-S cover Z_m.
        mmax = min(d * (d - 1) + 1, lib._moore_bound(d, 3) // 2)
        m = max(d + 1, best[0] // 2 + 1)  # only try orders that beat the current best
        while m <= mmax and time.monotonic() < deadline:
            now = time.monotonic()
            sub = now + 0.5 * (deadline - now)
            S = _search_S(m, d, rng, sub)
            if S is None:
                break
            n, edges = lib.haar_graph(m, S)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
            m += 1
    else:
        # Random Haar search for other diameters (parent's fallback).
        misses, m = 0, d + 1
        while time.monotonic() < deadline and misses < 10:
            found = None
            for _ in range(30):
                if time.monotonic() >= deadline:
                    break
                S = [0] + rng.sample(range(1, m), d - 1)
                n, edges = lib.haar_graph(m, S)
                if lib.within_diameter(n, edges, D):
                    found = (n, edges)
                    break
            if found:
                best, misses = found, 0
            else:
                misses += 1
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
