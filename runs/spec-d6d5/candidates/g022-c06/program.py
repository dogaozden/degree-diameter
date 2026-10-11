import math
import random
import time
from math import gcd

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over small groups, searched by hill-climbing.
#
# Group G of order m (cyclic or Z_m x| Z_k), mul(g, s), inverse table inv.
# Graph B(G, S), |S| = d, S a set of distinct elements containing the identity 0:
#     A-vertex g (index g) is adjacent to B-vertex h (index G + h) iff h = g*s, s in S.
# G acts by left multiplication, transitively on A and on B, so the diameter is
# at most D iff the eccentricity of a_1 and of b_1 are both at most D.
# Order is 2|G| and the graph is d-regular and bipartite.
#
# Search: hill-climb on S (one element replaced per move) minimising the number
# of vertices not within distance D of a_1 and of b_1.
# ----------------------------------------------------------------------------


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _random_group(G, rng):
    """Return (mul, inv) for a random semidirect product Z_m x| Z_k of order G, or None."""
    ks = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    rng.shuffle(ks)
    for k in ks[:6]:
        m = G // k
        if k == 1:
            rs = [1]
        else:
            rs = [r for r in range(1, m) if gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        r = rng.choice(rs)
        try:
            order, mul, inv = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        if order != G:
            continue
        return mul, inv
    return None


def _mul_table(G, mul):
    return [[mul(g, s) for s in range(G)] for g in range(G)]


def _count(start, S, Sinv, MT, G, D):
    """Number of vertices (of both sides) within distance D of `start` in B(G, S)."""
    seen = bytearray(2 * G)
    seen[start] = 1
    frontier = [start]
    count = 1
    for _ in range(D):
        nxt = []
        for v in frontier:
            if v < G:
                row = MT[v]
                for s in S:
                    w = G + row[s]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            else:
                row = MT[v - G]
                for si in Sinv:
                    w = row[si]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
        if not nxt:
            break
        count += len(nxt)
        frontier = nxt
    return count


def _cost(S, Sinv, MT, G, D):
    """Unreached (vertex, source) pairs from a_1 and from b_1. Zero iff diameter <= D."""
    ca = _count(0, S, Sinv, MT, G, D)
    cb = _count(G, S, Sinv, MT, G, D)
    return (2 * G - ca) + (2 * G - cb)


def _search_group(d, D, G, MT, inv, rng, deadline):
    """Hill-climb a connection set S (|S| = d, containing 0). Returns S or None."""
    if d < 2 or G <= d + 1:
        return None
    others = list(range(1, G))
    S = [0] + rng.sample(others, d - 1)
    Sinv = [inv[s] for s in S]
    c = _cost(S, Sinv, MT, G, D)
    T = 1.5
    while c > 0 and time.monotonic() < deadline:
        i = rng.randrange(1, d)
        cand = rng.randrange(1, G)
        if cand in S:
            continue
        S2 = S[:]
        S2[i] = cand
        Sinv2 = Sinv[:]
        Sinv2[i] = inv[cand]
        c2 = _cost(S2, Sinv2, MT, G, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, Sinv, c = S2, Sinv2, c2
        T = max(0.2, T * 0.995)
    return S if c == 0 else None


def _edges(G, MT, S):
    E = [(g, G + MT[g][s]) for g in range(G) for s in S]
    return 2 * G, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * time_limit, time_limit - 4.0)
    deadline = start + max(0.0, budget)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d >= 2:
        rng = random.Random(seed)
        while time.monotonic() < deadline:
            lo = best_n // 2 + 1
            G = lo + rng.randrange(0, 3)
            if G <= d + 1:
                G = d + 2
            g = _random_group(G, rng)
            if g is None:
                continue
            mul, inv = g
            MT = _mul_table(G, mul)
            inv_list = [inv(s) for s in range(G)]
            slice_end = min(deadline, time.monotonic() + 6.0)
            S = _search_group(d, D, G, MT, inv_list, rng, slice_end)
            if S is not None:
                n, e = _edges(G, MT, S)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
