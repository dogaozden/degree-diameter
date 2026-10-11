"""Degree-bounded bipartite growth with simulated-annealing repair.

Different from the voltage-lift search: start from K_{d,d} (valid for D >= 2),
then repeatedly add one vertex on each side. Each new vertex is wired in by
degree-preserving edge splits, and simulated annealing (2-switches, rewires,
and fill-in edges) drives the number of vertex pairs at distance > D to zero.
Every accepted state is valid by construction, and the best one is re-checked
with lib.is_valid before returning, with K_{d,d} as the fallback.
"""
import math
import random
import time

import lib


def _bad(N, adj, D):
    """Number of unordered vertex pairs at distance > D (bitmask balls)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _apply(adj, rem, add):
    for a, b in rem:
        adj[a].discard(b)
        adj[b].discard(a)
    for a, b in add:
        adj[a].add(b)
        adj[b].add(a)


def _kdd(d):
    adj = [set() for _ in range(2 * d)]
    color = [0] * d + [1] * d
    for a in range(d):
        for b in range(d, 2 * d):
            adj[a].add(b)
            adj[b].add(a)
    return adj, color


def _saturate(adj, color, d, rng):
    N = len(adj)
    dA = [v for v in range(N) if color[v] == 0 and len(adj[v]) < d]
    dB = [v for v in range(N) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in dA for b in dB if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d:
            adj[a].add(b)
            adj[b].add(a)


def _grow_pair(adj, color, d, rng):
    """Add one A vertex and one B vertex using degree-preserving edge splits."""
    a = len(adj)
    adj.append(set())
    color.append(0)
    b = len(adj)
    adj.append(set())
    color.append(1)
    A = [v for v in range(len(adj)) if color[v] == 0 and v != a]
    tries = 0
    while len(adj[a]) < d and len(adj[b]) < d and tries < 2000:
        tries += 1
        x = rng.choice(A)
        if not adj[x]:
            continue
        y = rng.choice(tuple(adj[x]))
        if y == b or x == a or y in adj[a] or x in adj[b]:
            continue
        # Split edge (x, y) into (a, y) and (x, b): degrees of x, y unchanged.
        adj[x].discard(y)
        adj[y].discard(x)
        adj[a].add(y)
        adj[y].add(a)
        adj[b].add(x)
        adj[x].add(b)
    _saturate(adj, color, d, rng)


def _anneal(adj, color, d, D, deadline, iters, rng):
    """Return True if the graph is brought to zero bad pairs within the budget."""
    N = len(adj)
    cost = _bad(N, adj, D)
    if cost == 0:
        return True
    A = [v for v in range(N) if color[v] == 0]
    B = [v for v in range(N) if color[v] == 1]
    for it in range(iters):
        if (it & 31) == 0 and time.monotonic() > deadline:
            return False
        T = 0.6 * (0.08 ** (it / iters))
        r = rng.random()
        if r < 0.15:
            dA = [a for a in A if len(adj[a]) < d]
            dB = [b for b in B if len(adj[b]) < d]
            if not dA or not dB:
                continue
            a = rng.choice(dA)
            b = rng.choice(dB)
            if b in adj[a]:
                continue
            rem, add = [], [(a, b)]
        elif r < 0.55:
            a1, a2 = rng.sample(A, 2)
            if not adj[a1] or not adj[a2]:
                continue
            b1 = rng.choice(tuple(adj[a1]))
            b2 = rng.choice(tuple(adj[a2]))
            if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
                continue
            rem = [(a1, b1), (a2, b2)]
            add = [(a1, b2), (a2, b1)]
        else:
            a1 = rng.choice(A)
            if not adj[a1]:
                continue
            b1 = rng.choice(tuple(adj[a1]))
            b2 = rng.choice(B)
            if b2 == b1 or b2 in adj[a1] or len(adj[b2]) >= d:
                continue
            rem = [(a1, b1)]
            add = [(a1, b2)]
        _apply(adj, rem, add)
        c2 = _bad(N, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                return True
        else:
            _apply(adj, add, rem)
    return cost == 0


def _edges(adj, color):
    return [(a, b) for a in range(len(adj)) if color[a] == 0 for b in adj[a]]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 0.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Safe fallback: K_{d,d}, valid for D >= 2.
    cur_adj, cur_col = _kdd(d)
    best_n = 2 * d
    best_e = _edges(cur_adj, cur_col)
    moore = lib.moore_bound(d, D)
    fails = 0

    while time.monotonic() < deadline and best_n + 2 <= moore:
        adj = [set(s) for s in cur_adj]
        col = list(cur_col)
        _grow_pair(adj, col, d, rng)
        iters = int(3000 * (1.5 ** min(fails, 6)))
        if _anneal(adj, col, d, D, deadline, iters, rng):
            cur_adj, cur_col = adj, col
            fails = 0
            best_n = len(adj)
            best_e = _edges(adj, col)
        else:
            fails += 1

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    fb_adj, fb_col = _kdd(d)
    return 2 * d, _edges(fb_adj, fb_col)
