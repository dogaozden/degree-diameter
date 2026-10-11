import math
import random
import time

import lib


def _bicayley_ok(m, adjA, adjB, D):
    """Check that the bi-Cayley graph has diameter <= D.

    The group acts regularly on each side, so distances from A_e and B_e
    determine the whole diameter.
    """
    n2 = 2 * m
    for s in (0, m):
        seen = bytearray(n2)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < m:
                    nb = [m + w for w in adjA[v]]
                else:
                    nb = adjB[v - m]
                for w in nb:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        if cnt != n2:
            return False
    return True


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * time_limit, max(0.2, time_limit - 3.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []

    # Projective-plane record when it applies (D = 3, d-1 a prime power).
    if D == 3 and lib.is_prime_power(d - 1):
        n, edges = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, edges, d, D):
            return n, edges

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_edges = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_edges, d, D):
        return 1, []

    # Bi-Cayley graphs over (possibly non-abelian) groups Z_a x| Z_b,
    # one vertex class per side, |S| = d. Order n = 2m with m = |G|.
    maxm = lib.moore_bound(d, D) // 2
    best_m = d
    rng = random.Random(seed)

    while best_m < maxm and time.monotonic() < deadline:
        span = maxm - best_m
        # Bias sampling toward small improvements over the current best.
        m = best_m + 1 + int(rng.random() ** 2 * span)
        if m > maxm:
            m = maxm

        divs = [a for a in range(2, m + 1) if m % a == 0]
        a = rng.choice(divs)
        b = m // a
        if b == 1:
            r = 1
        else:
            rs = [x for x in range(1, a)
                  if math.gcd(x, a) == 1 and pow(x, b, a) == 1 % a]
            if not rs:
                continue
            r = rng.choice(rs)

        order, mul, inv = lib.semidirect_group(a, b, r)
        if order != m:
            continue
        S = rng.sample(range(m), d)
        adjA = [[mul(x, g) for g in S] for x in range(m)]
        invS = [inv(g) for g in S]
        adjB = [[mul(y, h) for h in invS] for y in range(m)]

        if not _bicayley_ok(m, adjA, adjB, D):
            continue

        edges = [(x, m + y) for x in range(m) for y in adjA[x]]
        n = 2 * m
        if lib.is_valid(n, edges, d, D):
            best_m = m
            best_n, best_edges = n, edges

    return best_n, best_edges
