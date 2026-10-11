"""Bi-Cayley (Haar-type) search over non-abelian groups, with cyclic fallbacks.

Instead of multi-layer annealed voltage lifts, this program searches for a single
connection set S of size d inside a group G of order n/2 (|G| = G). The bipartite
graph has parts A_g and B_h with A_g ~ B_{g*s} for s in S. Left multiplication is an
automorphism that is transitive on each side, so diameter <= D only needs checking
from A_e and B_e. The search is a simulated-annealing hill-climb on S, run over a
sliding window of group orders just above the current best. Every improvement is
checked with lib.is_valid. The fallback is K_{d,d}, and for D = 3 the projective
plane incidence graph is tried first.
"""
import math
import random
import time

import lib


def _groups_of_order(G):
    """All semidirect products Z_m x| Z_k of order G as (m, k, r) triples (k=1 is cyclic)."""
    opts = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if k == 1:
            opts.append((m, 1, 1))
            continue
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _tables(G, mul, inv):
    """Full multiplication table and inverse list for a group of order G."""
    tab = [[mul(x, y) for y in range(G)] for x in range(G)]
    iv = [inv(x) for x in range(G)]
    return tab, iv


def _adjacency(G, tab, iv, S):
    """Adjacency lists of the bi-Cayley graph. A_g = g, B_h = G + h."""
    adjA = [[G + tab[g][s] for s in S] for g in range(G)]
    sinv = [iv[s] for s in S]
    adjB = [[tab[h][t] for t in sinv] for h in range(G)]
    return adjA + adjB


def _reached(adj, src, D):
    """Number of vertices within distance D of src."""
    seen = [False] * len(adj)
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
    return cnt


def _cost(G, tab, iv, S, D):
    """Unreached (vertex, source) pairs from A_e and B_e. Zero means diameter <= D."""
    adj = _adjacency(G, tab, iv, S)
    N = 2 * G
    return (N - _reached(adj, 0, D)) + (N - _reached(adj, G, D))


def _climb(G, tab, iv, d, D, rng, deadline, iters):
    """Annealed single-element swap hill-climb over d-subsets of the group."""
    S = rng.sample(range(G), d)
    c = _cost(G, tab, iv, S, D)
    T = 1.0
    for it in range(iters):
        if c == 0:
            return S
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(G)
        if x in S:
            continue
        i = rng.randrange(d)
        T2 = S[:]
        T2[i] = x
        c2 = _cost(G, tab, iv, T2, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = T2, c2
        T = max(0.2, T * 0.995)
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

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

    # D = 3: projective plane incidence graph for the largest q with q + 1 <= d.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break

    # Main search: bi-Cayley hill-climb over groups of growing order.
    # Each attempt picks a group order G in a window just above the best one,
    # then a random group of that order, then tries to find S of size d with diameter <= D.
    best_G = best_n // 2
    while time.monotonic() < deadline:
        lo = best_G + 1
        G = rng.randint(lo, lo + 6)
        opts = _groups_of_order(G)
        if not opts:
            continue
        m, k, r = rng.choice(opts)
        order, mul, inv = lib.semidirect_group(m, k, r)
        tab, iv = _tables(order, mul, inv)
        S = _climb(order, tab, iv, d, D, rng, deadline, 600)
        if S is None:
            continue
        edges = sorted({(g, order + tab[g][s]) for g in range(order) for s in S})
        n = 2 * order
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n
            best_G = order

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
