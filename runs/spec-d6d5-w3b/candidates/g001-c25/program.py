"""Bi-Cayley (vertex-transitive) search for bipartite graphs with max degree d and diameter D.

Construction: groups H of order G (semidirect products Z_m x| Z_k), connection set
S of d distinct elements. Vertices A_g and B_h (g, h in H); A_g ~ B_{gs} for s in S.
Left multiplication is an automorphism that is transitive on each side, so the
graph has diameter <= D iff the ball of radius D around A_1 and around B_1 covers
everything. Simulated annealing over S minimises the number of uncovered pairs.

Fallbacks: K_{d,d} (diameter 2), the projective-plane incidence graph (diameter 3),
and the cycle C_{2D} for d = 2. Every result is checked with lib.is_valid before
it is accepted.
"""
import math
import random
import time

import lib


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _missing(adj, src, N, D):
    """Number of vertices not within distance D of src."""
    seen = bytearray(N)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = 1
                    nxt.append(v)
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return N - cnt


def _sample_group(G, rng):
    """Return (m, k, r) with m * k = G, describing Z_m x| Z_k (cyclic if k = 1)."""
    ks = [k for k in range(2, G + 1) if G % k == 0 and G // k >= 2]
    if ks and rng.random() < 0.8:
        k = rng.choice(ks)
        m = G // k
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if cands:
            return m, k, rng.choice(cands)
    return G, 1, 1


def _search_bicayley(d, D, G, rng, deadline, iters):
    """Try to find a d-element connection set in a group of order G giving diameter <= D.

    Returns (n, edges) with n = 2G on success, otherwise None.
    """
    m, k, r = _sample_group(G, rng)
    _, mul, inv = lib.semidirect_group(m, k, r)
    fwd_cache, bwd_cache = {}, {}

    def fwd(s):
        p = fwd_cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(G)]
            fwd_cache[s] = p
        return p

    def bwd(s):
        p = bwd_cache.get(s)
        if p is None:
            si = inv(s)
            p = [mul(h, si) for h in range(G)]
            bwd_cache[s] = p
        return p

    def cost(S):
        N = 2 * G
        pf = [fwd(s) for s in S]
        pb = [bwd(s) for s in S]
        adj = [[G + p[g] for p in pf] for g in range(G)]
        adj += [[q[h] for q in pb] for h in range(G)]
        return _missing(adj, 0, N, D) + _missing(adj, G, N, D)

    S = rng.sample(range(G), d)
    cur = cost(S)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        c = cost(T)
        if c <= cur or rng.random() < 0.03:
            S, cur = T, c
    if cur != 0:
        return None
    edges = [(g, G + fwd(s)[g]) for g in range(G) for s in S]
    return 2 * G, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])

    moore = lib.moore_bound(d, D)
    rng = random.Random(seed * 1000003 + d * 131 + D)

    while best_n < moore and time.monotonic() < deadline:
        base = best_n // 2 + 1
        span = max(2, base // 30)
        G = base + rng.randrange(span)
        res = _search_bicayley(d, D, G, rng, deadline, 150)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
