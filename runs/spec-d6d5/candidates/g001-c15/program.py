import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline: incidence graph of PG(2, q), q the largest prime power with q+1 <= d.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _moore(d, D):
    """Moore-type bound for bipartite graphs with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


# ----------------------------------------------------------------------------
# New family: Haar graphs of non-abelian groups.
#
# Group Gamma of order G, connection set S = {s_1..s_d} (distinct elements,
# WLOG s_1 = identity). Vertices a_g = g and b_h = G + h, and edges
# a_g -- b_{g s} for every g and s in S. Degree is exactly d.
#
# Left multiplication by any x is an automorphism, and it is transitive on
# each side. So the graph has diameter <= D iff every vertex is within D of
# a_e and of b_e. The cost is the number of unreached vertices from those two
# sources, which is zero exactly when the graph is valid.
# ----------------------------------------------------------------------------

def _divisors(n):
    return [k for k in range(1, n + 1) if n % k == 0]


def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k of order G as (order, mul), or None."""
    ks = [k for k in _divisors(G) if k <= 12]
    for _ in range(40):
        k = rng.choice(ks)
        m = G // k
        if m < 2:
            continue
        if k == 1:
            r = 1
        else:
            pool = list(range(1, m))
            if len(pool) > 300:
                pool = rng.sample(pool, 300)
            good = [x for x in pool if math.gcd(x, m) == 1 and pow(x, k, m) == 1 % m]
            if not good:
                continue
            r = rng.choice(good)
        try:
            order, mul, _inv = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        return order, mul
    return None


def _cost(G, D, pairs):
    """Unreached (source, vertex) pairs for sources a_e and b_e. Zero means valid."""
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for pa, _pb in pairs:
                        v = G + pa[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    h = u - G
                    for _pa, pb in pairs:
                        v = pb[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - cnt
    return total


def _anneal_group(d, D, G, mul, rng, deadline, iters):
    """Simulated annealing over the connection set S (identity fixed in S)."""
    cache = {}

    def pair(s):
        pr = cache.get(s)
        if pr is None:
            pa = [mul(g, s) for g in range(G)]
            pb = [0] * G
            for g, h in enumerate(pa):
                pb[h] = g
            pr = (pa, pb)
            cache[s] = pr
        return pr

    S = [0] + rng.sample(range(1, G), d - 1)
    cost = _cost(G, D, [pair(s) for s in S])
    T = 1.5
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, G)
        if c in S:
            continue
        T2 = S[:]
        T2[i] = c
        c2 = _cost(G, D, [pair(s) for s in T2])
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S, cost = T2, c2
        T = max(0.05, T * 0.998)
    return S if cost == 0 else None


def _haar_from_group(G, mul, S):
    """Build the bipartite graph (2G vertices) for group order G and connection set S."""
    edges = []
    for s in S:
        for g in range(G):
            edges.append((g, G + mul(g, s)))
    return 2 * G, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    ceiling = _moore(d, D)
    while time.monotonic() < deadline and best_n < ceiling:
        lo = max(d, best_n // 2 + 1)
        G = lo + rng.randrange(0, max(3, lo // 25))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        if order < d:
            continue
        S = _anneal_group(d, D, order, mul, rng, deadline, iters=1200)
        if S is not None:
            n, e = _haar_from_group(order, mul, S)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
