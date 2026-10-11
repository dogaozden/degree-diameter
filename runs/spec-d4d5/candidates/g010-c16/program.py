"""Bi-Cayley (Haar-type) search over non-abelian groups for bipartite graphs.

Construction: pick a finite group G (semidirect product Z_m x| Z_k) and a
connection set S of d distinct elements. The graph has side A = {A_g} and side
B = {B_h}, with A_g adjacent to B_{g s} for each s in S. This is d-regular and
bipartite with 2|G| vertices.

Left multiplication by a group element is an automorphism that preserves both
sides. Therefore the diameter condition reduces to two BFS runs, one from A_e
and one from B_e. The search hill-climbs over S to drive the number of
unreached (source, vertex) pairs to zero. Every candidate is checked with
lib.is_valid before it is accepted. A projective-plane incidence graph and
K_{d,d} serve as fallbacks.

Note: this program has not been executed in this environment.
"""
import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_list(G, rng):
    """Candidate semidirect products Z_m x| Z_k of order G, as (m, k, r) triples, shuffled."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    rng.shuffle(out)
    return out


def _tables(G, m, k, r):
    """Multiplication and inverse tables for the group, or None if the parameters are invalid."""
    try:
        order, mul, inv = lib.semidirect_group(m, k, r)
    except ValueError:
        return None
    if order != G:
        return None
    mulT = [[mul(x, y) for y in range(G)] for x in range(G)]
    invT = [inv(x) for x in range(G)]
    return mulT, invT


def _adjacency(G, mulT, invT, S):
    """Combined adjacency on 2G vertices: A_g = g, B_h = G + h."""
    adj = [[] for _ in range(2 * G)]
    for g in range(G):
        for s in S:
            h = mulT[g][s]
            adj[g].append(G + h)
            adj[G + h].append(g)
    return adj


def _reached(adj, src, D, N):
    """Number of vertices within distance D of src."""
    seen = bytearray(N)
    seen[src] = 1
    frontier = [src]
    count = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = 1
                    nxt.append(v)
        if not nxt:
            break
        count += len(nxt)
        frontier = nxt
    return count


def _cost(G, mulT, invT, S, D):
    """Number of unreached pairs from A_e and B_e. Zero means the graph has diameter <= D."""
    N = 2 * G
    adj = _adjacency(G, mulT, invT, S)
    return (N - _reached(adj, 0, D, N)) + (N - _reached(adj, G, D, N))


def _search(G, mulT, invT, d, D, rng, deadline, iters):
    """Hill-climb a connection set S of d distinct group elements to zero cost."""
    S = rng.sample(range(G), d)
    c = _cost(G, mulT, invT, S, D)
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        ct = _cost(G, mulT, invT, T, D)
        if ct <= c or rng.random() < 0.02:
            S, c = T, ct
    return S if c == 0 else None


def _graph(G, mulT, S):
    """Edges of the Haar-type graph: A_g joined to B_{g s} for s in S."""
    edges = []
    for g in range(G):
        for s in S:
            edges.append((g, G + mulT[g][s]))
    return 2 * G, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])

        # Main search: bi-Cayley graphs over semidirect products, targeting orders above best.
        while time.monotonic() < deadline:
            lo = max(d + 1, best_n // 2 + 1)
            hi = lo + 24
            G = rng.randrange(lo, hi + 1)
            groups = _group_list(G, rng)
            tried = 0
            for m, k, r in groups:
                if time.monotonic() >= deadline or tried >= 6:
                    break
                tab = _tables(G, m, k, r)
                if tab is None:
                    continue
                tried += 1
                mulT, invT = tab
                S = _search(G, mulT, invT, d, D, rng, deadline, iters=600)
                if S is not None:
                    n, e = _graph(G, mulT, S)
                    consider(n, e)
                    if best_n >= 2 * G:
                        # A valid graph of this order exists; move the window upward.
                        pass
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
