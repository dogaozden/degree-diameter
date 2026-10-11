import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: bi-Cayley graphs over finite groups (one base vertex per side).
#
# Vertices A_g and B_h for g, h in a group G of order N. Connection set S of d
# distinct group elements gives edges A_g -- B_{g*s} for s in S. Left
# multiplication is an automorphism, so the graph is transitive on each side and
# diameter <= D reduces to two BFS runs, one from A_e and one from B_e. The
# search is annealing over S, with groups drawn from cyclic and semidirect
# products Z_m x| Z_k. Output size is 2N.
#
# Safe fallbacks: K_{d,d} (valid for D >= 2) and PG(2,q) incidence for D >= 3.
# Every candidate passes lib.is_valid before it can replace the best one.
# ----------------------------------------------------------------------------


def _pg_candidate(d):
    """Incidence graph of PG(2, q) with q = d - 1 if a small prime power (degree d)."""
    for q in range(d - 1, 1, -1):
        if q <= 30 and lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(G, rng):
    """Return (order, mul, inv) for a random group of order G (cyclic or Z_m x| Z_k), or None."""
    divs = [k for k in range(2, G) if G % k == 0 and G // k >= 2]
    if not divs or rng.random() < 0.15:
        return lib.cyclic_group(G)
    k = rng.choice(divs)
    m = G // k
    cands = [r for r in range(1, m)
             if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    if not cands:
        return None
    r = rng.choice(cands)
    try:
        return lib.semidirect_group(m, k, r)
    except ValueError:
        return None


def _mult_table(G, mul):
    return [[mul(x, y) for y in range(G)] for x in range(G)]


def _nbrs(G, M, inv_list, S):
    """Neighbour lists: nbA[g] = B-indices of A_g; nbB[h] = A-indices of B_h."""
    inv_S = [inv_list[s] for s in S]
    nbA = [[M[g][s] for s in S] for g in range(G)]
    nbB = [[M[h][si] for si in inv_S] for h in range(G)]
    return nbA, nbB


def _reach_cost(G, nbA, nbB, D):
    """Unreached (start, vertex) pairs over both start sides; zero means diameter <= D."""
    total = 0
    for start in (0, 1):
        seen = (bytearray(G), bytearray(G))
        seen[start][0] = 1
        cnt = [0, 0]
        cnt[start] = 1
        front = [0]
        side = start
        for _ in range(D):
            other = 1 - side
            nb = nbA if side == 0 else nbB
            so = seen[other]
            nxt = []
            for u in front:
                for v in nb[u]:
                    if not so[v]:
                        so[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt[other] += len(nxt)
            front = nxt
            side = other
        total += 2 * G - cnt[0] - cnt[1]
    return total


def _anneal_S(G, M, inv_list, d, D, rng, deadline):
    """Anneal a d-element connection set S in the group so the bi-Cayley graph has diameter <= D."""
    if G <= d:
        return None
    S = rng.sample(range(G), d)
    nbA, nbB = _nbrs(G, M, inv_list, S)
    cur = _reach_cost(G, nbA, nbB, D)
    T = 1.5
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        nA, nB = _nbrs(G, M, inv_list, S)
        c = _reach_cost(G, nA, nB, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            S[i] = old
        T = max(0.3, T * 0.999)
    if cur != 0:
        return None
    return S


def _bicayley_edges(G, M, S):
    """Edges A_g = g, B_h = G + h, with A_g -- B_{g*s} for s in S."""
    return [(g, G + M[g][s]) for g in range(G) for s in S]


def _kdd(d):
    """K_{d,d}: diameter 2, valid for D >= 2."""
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_e = _kdd(d)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    moore = lib.moore_bound(d, D)
    rng = random.Random(seed * 1000003 + d * 97 + D)
    attempt_budget = max(1.0, budget / 8.0)

    while time.monotonic() < deadline - 0.2 and best_n < moore:
        G = best_n // 2 + 1 + rng.randrange(0, 6)
        G = max(G, d + 2)
        if 2 * G > moore:
            G = moore // 2
        if G <= d + 1:
            break
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul, inv = g
        if order != G:
            continue
        M = _mult_table(G, mul)
        inv_list = [inv(x) for x in range(G)]
        attempt_end = min(deadline, time.monotonic() + attempt_budget)
        S = _anneal_S(G, M, inv_list, d, D, rng, attempt_end)
        if S is not None:
            consider(2 * G, _bicayley_edges(G, M, S))

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = _kdd(d)
    return best_n, best_e
