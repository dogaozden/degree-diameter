import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bold change: abelian Haar (bi-Cayley) lifts found by simulated annealing.
#
# Graph: parts A = {a_x} and B = {b_y}, x, y in an abelian group Gp of order G.
# Connection set S of d distinct group elements: a_x ~ b_{x+s} for s in S.
# Left translation and the side-swap a_x <-> b_{-x} are automorphisms, so the
# diameter is at most D iff the walk-balls from a_0 cover all of A and all of B.
# Walk sets are computed with boolean array indexing, so each cost evaluation
# is O(D * d) numpy operations.
#
# The group is Z_a x Z_b with a*b = G (b = 1 gives the cyclic group).
# Safe fallbacks: K_{d,d}, and PG(2,q) incidence graphs for D = 3.
# ----------------------------------------------------------------------------


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _tables(a, b):
    """Index tables for Z_a x Z_b with element (p, q) coded as p*b + q.

    Pl[s][x] = x + s and Mi[s][y] = y - s, both as element indices.
    """
    G = a * b
    x = np.arange(G, dtype=np.int64)
    P = x // b
    Q = x % b
    sp = P[:, None]
    sq = Q[:, None]
    Pl = ((P[None, :] + sp) % a) * b + (Q[None, :] + sq) % b
    Mi = ((P[None, :] - sp) % a) * b + (Q[None, :] - sq) % b
    return Mi, Pl


def _sa(G, d, D, Mi, Pl, rng, deadline):
    """Anneal a d-subset S of the group so that the Haar graph has diameter <= D.

    Returns S (list of group indices) on success, or None if the deadline passes.
    """

    def cost(S):
        a = np.zeros(G, dtype=bool)
        a[0] = True
        ball_a = a.copy()
        ball_b = np.zeros(G, dtype=bool)
        b = None
        for t in range(D):
            if t % 2 == 0:
                # Next B layer: b_y reached if a_{y-s} is reached for some s in S.
                b = np.zeros(G, dtype=bool)
                for s in S:
                    b |= a[Mi[s]]
                ball_b |= b
            else:
                # Next A layer: a_x reached if b_{x+s} is reached for some s in S.
                a = np.zeros(G, dtype=bool)
                for s in S:
                    a |= b[Pl[s]]
                ball_a |= a
        return 2 * G - int(ball_a.sum()) - int(ball_b.sum())

    S = rng.sample(range(G), d)
    c = cost(S)
    it = 0
    while c > 0:
        if (it & 31) == 0 and time.monotonic() > deadline:
            return None
        it += 1
        temp = 0.3 + 1.0 * math.exp(-it / 2000.0)
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = cost(S)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            c = c2
        else:
            S[i] = old
    return S


def _divisors_upto_sqrt(G):
    return [b for b in range(1, G + 1) if G % b == 0 and b * b <= G]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact construction for D = 3 when d - 1 is a prime power.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if d >= 3 and lib.is_prime_power(d - 1):
                return best

    # Moore bound: nothing larger is possible.
    if d == 2:
        moore = 2 * D
    else:
        moore = 2 * sum((d - 1) ** i for i in range(D))
    if best_n >= moore:
        return best

    # Main search: abelian Haar lifts with candidate group order G > best_n / 2.
    best_m = best_n // 2
    gap = max(2, best_m // 40)
    fails = 0
    while time.monotonic() < deadline:
        G = best_m + rng.randint(1, gap)
        G = max(G, d)
        divs = _divisors_upto_sqrt(G)
        if len(divs) == 1 or rng.random() < 0.5:
            b = 1
        else:
            b = rng.choice(divs)
        a = G // b
        Mi, Pl = _tables(a, b)
        slice_end = min(deadline, time.monotonic() + 2.5)
        S = _sa(G, d, D, Mi, Pl, rng, slice_end)
        if S is None:
            fails += 1
            gap = max(1, gap // 2)
            continue
        edges = [(x, G + int(Pl[s][x])) for s in S for x in range(G)]
        n = 2 * G
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n
            best_m = G
            gap = max(2, best_m // 40)
            if best_n >= moore:
                break
        else:
            fails += 1
            gap = max(1, gap // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
