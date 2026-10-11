"""Bold variant: grow a bipartite graph one vertex pair at a time and repair each
step with edge-move simulated annealing, minimising the number of vertex pairs
at distance > D. This replaces voltage-lift search with a repair search.

Start: incidence graph of PG(2, q) (q the largest prime power <= d-1) or K_{d,d},
whichever is larger and valid. Each growth step adds one A vertex and one B vertex,
then anneals edge moves (remove up to one edge at each endpoint that is full, then
add the new edge) until the cost is zero. Every accepted graph is checked with
lib.is_valid. The fallback K_{d,d} is always returned if anything fails.
"""
import math
import random
import time

import lib


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitmask BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _link(adj, aset, u, v):
    adj[u].append(v)
    adj[v].append(u)
    aset[u].add(v)
    aset[v].add(u)


def _unlink(adj, aset, u, v):
    adj[u].remove(v)
    adj[v].remove(u)
    aset[u].discard(v)
    aset[v].discard(u)


def _build(mA, mB, pairs):
    """Unified adjacency: A labels 0..mA-1, B labels mA..mA+mB-1."""
    n = mA + mB
    adj = [[] for _ in range(n)]
    aset = [set() for _ in range(n)]
    for a, b in pairs:
        _link(adj, aset, a, mA + b)
    return adj, aset


def _anneal(mA, mB, adj, aset, d, D, rng, deadline, iters, T0, T1):
    """Edge-move annealing. Moves keep max degree <= d and bipartiteness."""
    n = mA + mB
    cost = _bad_pairs(n, adj, D)
    if cost == 0:
        return 0
    decay = (T1 / T0) ** (1.0 / max(1, iters))
    T = T0
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T *= decay
        # Bias some moves towards the newest (lowest-degree) vertices.
        a = mA - 1 if rng.random() < 0.15 else rng.randrange(mA)
        b = n - 1 if rng.random() < 0.15 else mA + rng.randrange(mB)
        if b in aset[a]:
            continue
        removed = []
        if len(adj[a]) >= d:
            x = adj[a][rng.randrange(len(adj[a]))]
            removed.append((a, x))
        if len(adj[b]) >= d:
            y = adj[b][rng.randrange(len(adj[b]))]
            removed.append((y, b))
        for u, v in removed:
            _unlink(adj, aset, u, v)
        _link(adj, aset, a, b)
        new = _bad_pairs(n, adj, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
        else:
            _unlink(adj, aset, a, b)
            for u, v in removed:
                _link(adj, aset, u, v)
    return cost


def _largest_pg_q(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def build(d, D, seed, time_limit):
    start_time = time.monotonic()
    deadline = start_time + max(0.5, 0.8 * time_limit - 1.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    rng = random.Random(seed * 1000003 + d * 101 + D)

    # Safe fallback: K_{d,d}, diameter 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best_n, best_e = fb_n, fb_e

    # Starting graph: K_{d,d}, or PG(2,q) when D >= 3 and it is larger.
    mA = mB = d
    pairs = [(i, j) for i in range(d) for j in range(d)]
    if D >= 3:
        q = _largest_pg_q(d)
        if q is not None:
            pn, pe = lib.projective_plane_incidence(q)
            m = pn // 2
            if pn > best_n and lib.is_valid(pn, pe, d, D):
                mA = mB = m
                pairs = [(u, v - m) for u, v in pe]
                best_n, best_e = pn, pe

    moore = lib._moore_bound(d, D)
    best_n_cur = mA + mB
    if best_n_cur < best_n:
        best_n_cur = best_n

    fails = 0
    while time.monotonic() < deadline and fails < 60:
        if mA + mB + 2 > moore:
            break
        nA, nB = mA + 1, mB + 1
        adj, aset = _build(nA, nB, pairs)
        cost = _anneal(nA, nB, adj, aset, d, D, rng, deadline,
                       iters=2000, T0=1.0, T1=0.1)
        if cost == 0:
            n = nA + nB
            e = [(v, u) for v in range(nA) for u in adj[v]]
            if lib.is_valid(n, e, d, D):
                mA, mB = nA, nB
                pairs = [(v, u - nA) for v in range(nA) for u in adj[v]]
                if n > best_n:
                    best_n, best_e = n, e
                fails = 0
                continue
        fails += 1

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = fb_n, fb_e
    return best_n, best_e
