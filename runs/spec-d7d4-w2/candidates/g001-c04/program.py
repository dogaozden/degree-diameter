import math
import random
import time

import lib


def _unreached(m, S, D, from_a):
    """Count vertices of Haar graph H(Z_m, S) not within distance D of a_0 (from_a) or b_0 (not from_a)."""
    seen_a = bytearray(m)
    seen_b = bytearray(m)
    if from_a:
        seen_a[0] = 1
        fa, fb = [0], []
    else:
        seen_b[0] = 1
        fa, fb = [], [0]
    for _ in range(D):
        nb = []
        for i in fa:                      # a_i -- b_{i+s}
            for s in S:
                j = i + s
                if j >= m:
                    j -= m
                if not seen_b[j]:
                    seen_b[j] = 1
                    nb.append(j)
        na = []
        for j in fb:                      # b_j -- a_{j-s}
            for s in S:
                i = j - s
                if i < 0:
                    i += m
                if not seen_a[i]:
                    seen_a[i] = 1
                    na.append(i)
        fa, fb = na, nb
        if not fa and not fb:
            break
    return 2 * m - (sum(seen_a) + sum(seen_b))


def _cost(m, S, D):
    """Zero iff the Haar graph H(Z_m, S) has diameter <= D (by Z_m-transitivity it suffices to check from a_0 and b_0)."""
    return _unreached(m, S, D, True) + _unreached(m, S, D, False)


def _anneal(m, d, D, rng, deadline):
    """Simulated annealing over connection sets S (containing 0, WLOG) of size d in Z_m."""
    S = [0] + rng.sample(range(1, m), d - 1)
    cur = _cost(m, S, D)
    while cur > 0 and time.monotonic() < deadline:
        k = rng.randrange(1, d)
        new = rng.randrange(1, m)
        if new in S:
            continue
        S2 = S[:]
        S2[k] = new
        c2 = _cost(m, S2, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / 0.7):
            S, cur = S2, c2
    return S if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 1.0)

    # Degenerate cases.
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # D = 3 with d-1 a prime power: projective plane incidence graph meets the Moore bound.
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    # Fallback: K_{d,d} (diameter 2 <= D).
    n0, e0 = lib.haar_graph(d, range(d))
    best = (n0, e0) if lib.is_valid(n0, e0, d, D) else (2, [(0, 1)])

    rng = random.Random(seed)
    moore = lib.moore_bound(d, D)
    total = deadline - start
    per_attempt = max(1.0, 0.08 * total)   # time budget for one value of m

    m = d + 1
    fails = 0
    while time.monotonic() < deadline and fails < 2 and 2 * m <= moore:
        attempt_deadline = min(deadline, time.monotonic() + per_attempt)
        S = _anneal(m, d, D, rng, attempt_deadline)
        if S is not None:
            n, edges = lib.haar_graph(m, S)
            if lib.is_valid(n, edges, d, D) and n > best[0]:
                best = (n, edges)
                fails = 0
            else:
                fails += 1
        else:
            fails += 1
        m += 1

    return best
