"""Bipartite degree-diameter search by simulated annealing over edge switches.

Strategy (replaces the previous voltage-lift and cover-growth pipeline):
  * Work with d-regular bipartite graphs on two sides of size s.
  * Start from the circulant graph (a, (a+k) mod s), which is simple and valid.
  * Anneal with degree-preserving edge switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1),
    minimising the number of vertex pairs at distance > D.
  * Climb the side size s one step at a time; each success is checked with
    lib.is_valid and kept. A failed attempt ends the ladder.
  * Fallback is K_{d,d}, and PG(2,q) is used for D = 3 when available.
"""
import math
import random
import time

import lib


FRAC_END = 0.85  # fraction of time_limit we are willing to use


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bad_pairs_adj(adj, N, D):
    """Number of unordered vertex pairs at distance > D (0 means valid diameter)."""
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(N - x.bit_count() for x in ball) // 2


def _swap(lst, old, new):
    i = lst.index(old)
    lst[i] = new


def _anneal_regular(s, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph with sides of size s; return edges or None."""
    if s < d:
        return None
    N = 2 * s
    # Side A: nodes 0..s-1. Side B: nodes s..2s-1.
    adj = [[] for _ in range(N)]
    M = [bytearray(s) for _ in range(s)]
    for a in range(s):
        for k in range(d):
            b = (a + k) % s
            adj[a].append(s + b)
            adj[s + b].append(a)
            M[a][b] = 1

    def apply(a1, a2, b1, b2):
        """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1)."""
        B1, B2 = s + b1, s + b2
        _swap(adj[a1], B1, B2)
        _swap(adj[a2], B2, B1)
        _swap(adj[B1], a1, a2)
        _swap(adj[B2], a2, a1)
        M[a1][b1] = 0
        M[a2][b2] = 0
        M[a1][b2] = 1
        M[a2][b1] = 1

    cur = _bad_pairs_adj(adj, N, D)
    T0, T1 = 2.0, 0.05
    t_begin = time.monotonic()
    span = max(1e-3, deadline - t_begin)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - t_begin) / span)
        T = T0 * (T1 / T0) ** frac

        a1 = rng.randrange(s)
        a2 = rng.randrange(s)
        if a1 == a2:
            continue
        b1 = adj[a1][rng.randrange(d)] - s
        b2 = adj[a2][rng.randrange(d)] - s
        if b1 == b2 or M[a1][b2] or M[a2][b1]:
            continue

        apply(a1, a2, b1, b2)
        new = _bad_pairs_adj(adj, N, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            apply(a1, a2, b2, b1)  # undo

    if cur != 0:
        return None
    edges = []
    for a in range(s):
        for B in adj[a]:
            edges.append((a, B))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + FRAC_END * time_limit
    rng = random.Random(seed * 1000003 + d * 31 + D)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D  # even cycle: bipartite, diameter D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # K_{d,d} has diameter 2 and is the always-valid fallback.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback
    moore = lib.moore_bound(d, D)

    if D == 3:
        try:
            pg = _pg_candidate(d)
            if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
                best = pg
        except Exception:
            pass
        if best[0] >= moore:
            return best

    # Ladder over side sizes s for d-regular bipartite graphs.
    try:
        s = best[0] // 2 + 1
        while True:
            now = time.monotonic()
            rem = end - now
            if rem < 0.5 or 2 * s > moore:
                break
            budget = max(0.5, 0.6 * rem)
            edges = _anneal_regular(s, d, D, rng, now + budget)
            if edges is None:
                break
            n = 2 * s
            if lib.is_valid(n, edges, d, D) and n > best[0]:
                best = (n, edges)
                s += 1
            else:
                break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
