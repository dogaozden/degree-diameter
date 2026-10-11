import math
import random
import time

import lib


def _rot(x, k, m, full):
    """Rotate the m-bit set x so that bit i moves to bit (i + k) mod m."""
    if k == 0:
        return x
    return ((x << k) | (x >> (m - k))) & full


def _cost(m, S, D):
    """Number of (side, vertex) pairs not within distance D of a_0 or b_0 in Haar(m, S).

    The rotation i -> i+1 is an automorphism of Haar(m, S) that preserves both sides,
    so every pair of vertices is equivalent to a pair involving a_0 or b_0. Zero cost
    therefore means the graph has diameter <= D.
    """
    full = (1 << m) - 1
    total = 0
    for from_a in (True, False):
        ra, rb = (1, 0) if from_a else (0, 1)
        for _ in range(D):
            na, nb = ra, rb
            for s in S:
                # a_i ~ b_{i+s}: B-set -> A-set rotates by -s, A-set -> B-set rotates by +s.
                na |= _rot(rb, (m - s) % m, m, full)
                nb |= _rot(ra, s, m, full)
            ra, rb = na & full, nb & full
        total += (m - ra.bit_count()) + (m - rb.bit_count())
    return total


def _anneal(m, d, D, rng, iters, deadline):
    """Simulated annealing over connection sets S (containing 0) of size d in Z_m."""
    S = [0] + rng.sample(range(1, m), d - 1)
    cur = _cost(m, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if (it & 255) == 0 and time.monotonic() >= deadline:
            break
        temp = 1.0 * (1.0 - it / iters) + 0.02
        i = rng.randrange(1, d)
        new_v = rng.randrange(1, m)
        if new_v in S:
            continue
        T = S[:]
        T[i] = new_v
        c = _cost(m, T, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            S, cur = T, c
    return S if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    if d < 2:
        return best
    bound = lib.moore_bound(d, D)
    iters = 4000
    m = d + 1
    while time.monotonic() < deadline and 2 * m <= bound:
        S = _anneal(m, d, D, rng, iters, deadline)
        if S is not None:
            n, edges = lib.haar_graph(m, S)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        m += 1
    return best
