"""Bi-Cayley search for bipartite graphs with max degree d and diameter D.

Vertices: a_g and b_h for g, h in a finite group G of order n/2.
Edges:    a_g ~ b_{g*s} for every s in S, where |S| = d.

Left multiplication by G is an automorphism that preserves both sides, so
every distance reduces to two BFS runs, from a_e and from b_e. The main
family is searched over semidirect products Z_m x| Z_k with random connection
sets S, using hill-climbing on the number of unreached (source, vertex) pairs.
Projective-plane incidence graphs and K_{d,d} serve as always-valid fallbacks.
"""

import math
import random
import time

import lib


TIME_FRAC = 0.85     # fraction of time_limit we are willing to use
SLICE = 1.5          # seconds spent on each group order before moving on
MAX_ORDER = 300      # cap on group order (keeps the multiplication table small)
STEPS = 350          # hill-climb steps per restart
RESTARTS = 4         # restarts per sampled group


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (diameter 3, degree q+1)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_specs(G):
    """All (m, k, r) with Z_m x| Z_k of order G (r = 1 gives the direct product, k = 1 gives Z_G)."""
    specs = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if k == 1:
            specs.append((m, 1, 1))
            continue
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        specs.extend((m, k, r) for r in rs)
    return specs


def _tables(spec):
    """Return (order, right-multiplication table, inverse list) for a semidirect product."""
    m, k, r = spec
    G, mul, inv = lib.semidirect_group(m, k, r)
    tab = [[mul(g, s) for s in range(G)] for g in range(G)]
    invs = [inv(s) for s in range(G)]
    return G, tab, invs


def _adjacency(G, tab, invs, S):
    """Adjacency lists of the bi-Cayley graph: a_g = g, b_h = G + h."""
    Sinv = [invs[s] for s in S]
    adj = [None] * (2 * G)
    for g in range(G):
        row = tab[g]
        adj[g] = [G + row[s] for s in S]      # a_g ~ b_{g s}
        adj[G + g] = [row[t] for t in Sinv]   # b_h ~ a_{h s^-1}
    return adj


def _reach(adj, src, D, N):
    """Number of vertices within distance D of src."""
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
    return cnt


def _cost(G, tab, invs, S, D):
    """Unreached (source, vertex) pairs from a_e and b_e. Zero means diameter <= D."""
    adj = _adjacency(G, tab, invs, S)
    N = 2 * G
    return (N - _reach(adj, 0, D, N)) + (N - _reach(adj, G, D, N))


def _climb(G, tab, invs, d, D, rng, steps, deadline):
    """Hill-climb a connection set S of size d; return it if the cost reaches zero."""
    S = rng.sample(range(G), d)
    cost = _cost(G, tab, invs, S, D)
    for _ in range(steps):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        c = _cost(G, tab, invs, T, D)
        if c <= cost or rng.random() < 0.03:
            S, cost = T, c
    return S if cost == 0 else None


def _search_order(G, d, D, rng, deadline):
    """Try random groups of order G until a valid connection set is found; return (n, edges) or None."""
    specs = _group_specs(G)
    if not specs:
        return None
    while time.monotonic() < deadline:
        spec = rng.choice(specs)
        Gg, tab, invs = _tables(spec)
        for _ in range(RESTARTS):
            if time.monotonic() >= deadline:
                break
            S = _climb(Gg, tab, invs, d, D, rng, STEPS, deadline)
            if S is not None:
                edges = [(g, Gg + tab[g][s]) for g in range(Gg) for s in S]
                return 2 * Gg, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + TIME_FRAC * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D                       # even cycle: bipartite, diameter D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # K_{d,d} has diameter 2 and is the always-valid fallback.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback
    moore = lib.moore_bound(d, D)

    # Projective-plane incidence graph (diameter 3) as an algebraic start.
    if D >= 3:
        try:
            pg = _pg_candidate(d)
        except Exception:
            pg = None
        if pg is not None and lib.is_valid(pg[0], pg[1], d, D) and pg[0] > best[0]:
            best = pg
        if best[0] >= moore:
            return best

    # Bi-Cayley sweep over increasing group orders.
    try:
        if d >= 3:
            G = max(2, best[0] // 2 + 1)
            while (time.monotonic() < deadline
                   and G <= min(MAX_ORDER, moore // 2)):
                slice_end = min(deadline, time.monotonic() + SLICE)
                found = _search_order(G, d, D, rng, slice_end)
                if found is not None:
                    n, e = found
                    if n > best[0] and lib.is_valid(n, e, d, D):
                        best = (n, e)
                G += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
