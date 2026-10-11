"""Weighted twin blow-up of projective-plane incidence graphs.

Idea (new relative to the parent): a vertex can be duplicated into w_v copies that
share the same neighbourhood. Copies of one vertex are at distance 2, and every
other distance is inherited from the base graph, so a diameter-D base stays
diameter-D after blow-up. Copy degrees are sums of neighbouring weights, so the
problem becomes: choose integer weights w >= 1 on the base vertices such that for
every base vertex v, sum of w over its neighbours is at most d, maximising sum(w).

For PG(2,q) with d = q+3 this is solved by a conic seed (weight 2 on a conic and
its dual conic). Local search (kick and greedy refill, with revert) then tries to
improve it. The result is validated with lib.is_valid, and the fallback is K_{d,d}.
"""
import math
import random
import time

import lib


def _loads(nb, N, w):
    """load[v] = sum of weights over the neighbours of v (= degree of each copy of v)."""
    return [sum(w[u] for u in nb[v]) for v in range(N)]


def _refill(nb, N, d, w, load, rng):
    """Greedily increase weights in random order while every neighbour load stays <= d."""
    order = list(range(N))
    rng.shuffle(order)
    for u in order:
        nbu = nb[u]
        if not nbu:
            continue
        while all(load[v] < d for v in nbu):
            w[u] += 1
            for v in nbu:
                load[v] += 1


def _ils(nb, N, d, w, rng, deadline):
    """Iterated local search on the weights: kick a few extras down, refill, accept if not worse."""
    load = _loads(nb, N, w)
    _refill(nb, N, d, w, load, rng)
    best = w[:]
    best_s = sum(w)
    cur = best_s
    while time.monotonic() < deadline:
        extras = [u for u in range(N) if w[u] > 1]
        if not extras:
            break
        save_w = w[:]
        k = min(len(extras), rng.randint(1, 3))
        for u in rng.sample(extras, k):
            w[u] -= 1
            for v in nb[u]:
                load[v] -= 1
        _refill(nb, N, d, w, load, rng)
        s = sum(w)
        if s >= cur:
            cur = s
            if s > best_s:
                best_s = s
                best = w[:]
        else:
            w[:] = save_w
            load[:] = _loads(nb, N, w)
    return best, best_s


def _blow(base_n, base_edges, w):
    """Blow up each base vertex u into w[u] copies; each base edge becomes a complete bipartite join."""
    copies = []
    n = 0
    for u in range(base_n):
        copies.append(list(range(n, n + w[u])))
        n += w[u]
    edges = []
    for u, v in base_edges:
        for a in copies[u]:
            for b in copies[v]:
                edges.append((a, b))
    return n, edges


def _conic_seed(q, m, pts):
    """Base-vertex indices of a conic (plus nucleus for even q), as points and as dual lines.

    The same coordinate vectors are used for points (index i) and lines (index m + i).
    Both sets are arcs, so every line meets the point seed in <= 2 points and every
    point lies on <= 2 seeded lines.
    """
    F = lib.GF(q)
    idx = {p: i for i, p in enumerate(pts)}
    S = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if q % 2 == 0:
        S.append((0, 1, 0))
    seeds = []
    for p in S:
        i = idx[p]
        seeds.append(i)
        seeds.append(m + i)
    return seeds


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Degree-2 case: even cycle C_{2D} has diameter D.
    if d == 2 and D >= 2:
        L = 2 * D
        consider(L, [(i, (i + 1) % L) for i in range(L)])

    if D >= 3:
        cands = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        for idx, q in enumerate(cands):
            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0:
                break
            share = 0.9 if idx == 0 else 0.1 / max(1, len(cands) - 1)
            t_end = now + share * remaining

            base_n, base_edges = lib.projective_plane_incidence(q)
            m = base_n // 2
            nb = lib.adjacency(base_n, base_edges)
            pts = lib.projective_points(q)

            w = [1] * base_n
            seeds = _conic_seed(q, m, pts)
            for s_idx in seeds:
                w[s_idx] = 2
            if max(_loads(nb, base_n, w), default=0) > d:
                w = [1] * base_n  # seed infeasible for this (q, d): start from scratch

            w, _ = _ils(nb, base_n, d, w, rng, t_end)
            n, E = _blow(base_n, base_edges, w)
            consider(n, E)

    return best_n, best_e
