import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic baselines: projective plane incidence and the Araujo-Pardo-Lopez
# record graph for d = q + 2 (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New routine: bi-Cayley graphs over arbitrary finite groups.
#
# For a group G (order g) and a connection set S of d distinct elements with
# identity in S, the bipartite graph on A = {a_x} and B = {b_x} with
# a_x ~ b_{x*s} for s in S is d-regular on 2g vertices.
#
# Left multiplication by h maps a_x -> a_{hx}, b_x -> b_{hx}, an automorphism.
# So A and B are each vertex-transitive, and the diameter is at most D iff the
# eccentricities of a_e and b_e are both at most D. Only two BFS runs are
# needed per candidate S, which makes the hill-climb over S cheap.
# Translating S on the right gives an isomorphic graph, so we fix e in S.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random group of order G: semidirect product Z_m x| Z_k (k | G), with r = 1 giving direct products."""
    k2s = [k for k in range(1, 13) if G % k == 0 and G // k >= 2]
    if not k2s:
        return None
    for _ in range(60):
        k2 = rng.choice(k2s)
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(40):
                cand = rng.randrange(1, m)
                if math.gcd(cand, m) == 1 and pow(cand, k2, m) == 1 % m:
                    r = cand
                    break
            if r is None:
                continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _bicayley_cost(G, D, perm_of, S):
    """Unreached (vertex, source) pairs from a_e and b_e within distance D. Zero iff valid."""
    N = 2 * G
    adj = [[] for _ in range(N)]
    for s in S:
        p = perm_of(s)
        for g in range(G):
            b = G + p[g]
            adj[g].append(b)
            adj[b].append(g)
    total = 0
    for src in (0, G):
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
    return total


def _hill_connection_set(d, D, G, mul, rng, deadline):
    """Anneal a connection set S (|S| = d, identity included) so that the bi-Cayley graph has diameter <= D."""
    if G < d + 1:
        return None
    cache = {}

    def perm_of(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(G)]
            cache[s] = p
        return p

    S = [0] + rng.sample(range(1, G), d - 1)
    c = _bicayley_cost(G, D, perm_of, S)
    temp = 0.6
    while c > 0 and time.monotonic() < deadline:
        i = rng.randrange(1, d)
        x = rng.randrange(1, G)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        c2 = _bicayley_cost(G, D, perm_of, T)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            S, c = T, c2
        temp = max(0.05, temp * 0.995)
    return S if c == 0 else None


def _bicayley_edges(G, mul, S):
    """Edge list of the bi-Cayley graph: a_x ~ b_{x*s} for s in S."""
    edges = []
    for s in S:
        for g in range(G):
            edges.append((g, G + mul(g, s)))
    return 2 * G, edges


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # New search: bi-Cayley graphs over random groups, just above the current order.
    if D >= 4 and d >= 2:
        while time.monotonic() < deadline:
            G = best_n // 2 + 1 + rng.randrange(0, 6)
            if G < d + 1:
                G = d + 1
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            slice_end = min(deadline, time.monotonic() + 3.0)
            S = _hill_connection_set(d, D, order, mul, rng, slice_end)
            if S is not None:
                n, e = _bicayley_edges(order, mul, S)
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
