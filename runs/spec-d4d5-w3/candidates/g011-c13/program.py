"""Unstructured repair search for bipartite diameter-D graphs.

Instead of algebraic lifts, this starts from a random d-regular bipartite graph on
M + M vertices and anneals double-edge switches (which preserve regularity and
bipartiteness) to minimise the number of vertex pairs at distance more than D.
M is increased one step at a time after each success. The best valid graph found
so far is always returned, starting from K_{d,d} and the projective-plane graph.
"""
import math
import random
import time

import lib


def _bad_pairs(N, nb, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _random_regular(M, d, rng):
    """d edge-disjoint perfect matchings between M A-vertices and M B-vertices, or None."""
    used = [set() for _ in range(M)]
    perms = []
    for _ in range(d):
        ok = False
        for _try in range(3000):
            p = list(range(M))
            rng.shuffle(p)
            if all(p[i] not in used[i] for i in range(M)):
                ok = True
                break
        if not ok:
            return None
        for i in range(M):
            used[i].add(p[i])
        perms.append(p)
    return perms


def _switch(nb, Bm, M, rem, add):
    """Remove the pairs in rem and add the pairs in add (pairs are (A index, B index))."""
    for a, b in rem:
        Bm[a][b] = 0
        nb[a].remove(M + b)
        nb[M + b].remove(a)
    for a, b in add:
        Bm[a][b] = 1
        nb[a].append(M + b)
        nb[M + b].append(a)


def _anneal(M, d, D, rng, deadline):
    """Anneal a random d-regular bipartite graph on M+M vertices; return (ea, eb) on success."""
    N = 2 * M
    perms = _random_regular(M, d, rng)
    if perms is None:
        return None
    nb = [[] for _ in range(N)]
    Bm = [[0] * M for _ in range(M)]
    ea, eb = [], []
    for p in perms:
        for i in range(M):
            j = p[i]
            Bm[i][j] = 1
            nb[i].append(M + j)
            nb[M + j].append(i)
            ea.append(i)
            eb.append(j)
    E = len(ea)
    cost = _bad_pairs(N, nb, D)
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = 0.12 + 0.9 * (1.0 - (now - t_start) / span)
        e1 = rng.randrange(E)
        e2 = rng.randrange(E)
        a1, b1, a2, b2 = ea[e1], eb[e1], ea[e2], eb[e2]
        if a1 == a2 or b1 == b2 or Bm[a1][b2] or Bm[a2][b1]:
            continue
        _switch(nb, Bm, M, [(a1, b1), (a2, b2)], [(a1, b2), (a2, b1)])
        c2 = _bad_pairs(N, nb, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            ea[e1], eb[e1] = a1, b2
            ea[e2], eb[e2] = a2, b1
        else:
            _switch(nb, Bm, M, [(a1, b2), (a2, b1)], [(a1, b1), (a2, b2)])
    return ea, eb


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit - 0.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe baseline: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    # Projective plane incidence graph (diameter 3) for the largest prime power q <= d-1.
    if D >= 3:
        for q in range(min(d - 1, 23), 1, -1):
            if lib.is_prime_power(q):
                cand = lib.projective_plane_incidence(q)
                if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                    best = cand
                break

    # Calibration-style cases (D <= 3) return the known construction immediately.
    if D >= 4 and d >= 3:
        M = best[0] // 2 + 1
        while time.monotonic() < end:
            now = time.monotonic()
            remaining = end - now
            budget = min(remaining, max(5.0, 0.35 * remaining))
            res = _anneal(M, d, D, rng, now + budget)
            if res is None:
                continue
            ea, eb = res
            N = 2 * M
            edges = [(ea[e], M + eb[e]) for e in range(len(ea))]
            if N > best[0] and lib.is_valid(N, edges, d, D):
                best = (N, edges)
            M += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])
    return best
