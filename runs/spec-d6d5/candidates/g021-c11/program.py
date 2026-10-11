import math
import random
import time

import lib


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _unreached(n, adj, D):
    """Number of ordered vertex pairs at distance more than D (zero means diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _random_switch(adj, h, d, rng):
    """Propose a double edge switch a-b, c-dd -> a-dd, c-b. Left side is 0..h-1, right is h..2h-1."""
    a = rng.randrange(h)
    b = adj[a][rng.randrange(d)]
    c = rng.randrange(h)
    if c == a:
        return None
    dd = adj[c][rng.randrange(d)]
    if dd in adj[a] or b in adj[c]:
        return None
    return a, b, c, dd


def _apply(adj, a, b, c, dd):
    adj[a][adj[a].index(b)] = dd
    adj[c][adj[c].index(dd)] = b
    adj[b][adj[b].index(a)] = c
    adj[dd][adj[dd].index(c)] = a


def _undo(adj, a, b, c, dd):
    _apply(adj, a, dd, c, b)


def _anneal_bip(h, d, D, rng, deadline):
    """Anneal a random d-regular bipartite graph on 2h vertices (sides h, h) by double edge switches.

    Start from a Haar graph with random shift set, mix, then minimise unreached pairs.
    Returns (n, edges) with zero unreached pairs, or None if the deadline passes first.
    """
    n = 2 * h
    S = rng.sample(range(h), d)
    adj = [[] for _ in range(n)]
    for i in range(h):
        for s in S:
            j = h + (i + s) % h
            adj[i].append(j)
            adj[j].append(i)
    for _ in range(4 * h):
        mv = _random_switch(adj, h, d, rng)
        if mv is not None:
            _apply(adj, *mv)

    cur = _unreached(n, adj, D)
    T = 3.0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        mv = _random_switch(adj, h, d, rng)
        if mv is None:
            continue
        _apply(adj, *mv)
        new = _unreached(n, adj, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            _undo(adj, *mv)
        T = max(0.3, T * 0.9995)

    edges = [(i, j) for i in range(h) for j in adj[i]]
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None and pg[0] > best_n and lib.is_valid(pg[0], pg[1], d, D):
            best_n, best_e = pg

    if D >= 4 and d >= 3:
        # Adaptive ladder over the side size h: grow on success, shrink the step on failure.
        h_best = best_n // 2
        step = 64
        while time.monotonic() < deadline:
            h = h_best + step
            now = time.monotonic()
            remaining = deadline - now
            budget = min(remaining, max(2.0, 0.3 * remaining))
            res = _anneal_bip(h, d, D, rng, now + budget)
            if res is not None and lib.is_valid(res[0], res[1], d, D):
                best_n, best_e = res
                h_best = h
                step = min(2 * step, 32)
            else:
                step = max(1, step // 2)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
