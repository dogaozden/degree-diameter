"""Bold variant for d=6, D=5: random bipartite regular graphs repaired by edge switches.

Instead of Haar graphs over a group, this builds a bipartite d-regular graph with sides of size s (2s vertices).
It starts from the circulant Haar graph with shifts 0..d-1, randomizes it with edge switches, then runs a
Metropolis hill-climb on the number of vertex pairs at distance > D. Every switch keeps the graph simple,
bipartite and d-regular. Sizes are tried in an increasing ladder, and every candidate is checked with
lib.is_valid before it is kept. If nothing larger succeeds, the best valid graph found so far is returned,
and the tiny always-valid graph covers the rest.
"""
import math
import random
import time

import lib


TARGET = (6, 5)


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _cost(adj, N, D):
    """Number of ordered vertex pairs at distance > D (0 means diameter <= D)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        nxt = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(N - r.bit_count() for r in reach)


def _initial(s, d):
    """Circulant Haar graph with shifts 0..d-1: simple, bipartite, d-regular (needs s >= d)."""
    E = [(i, s + (i + k) % s) for i in range(s) for k in range(d)]
    eset = set(E)
    adj = [[] for _ in range(2 * s)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    return E, eset, adj


def _ok(E, eset, i, j):
    """A switch of edges i and j is legal iff the two new edges are fresh and not degenerate."""
    a1, b1 = E[i]
    a2, b2 = E[j]
    return a1 != a2 and b1 != b2 and (a1, b2) not in eset and (a2, b1) not in eset


def _switch(E, eset, adj, i, j):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Applying it twice restores the original."""
    a1, b1 = E[i]
    a2, b2 = E[j]
    n1, n2 = (a1, b2), (a2, b1)
    eset.discard((a1, b1))
    eset.discard((a2, b2))
    eset.add(n1)
    eset.add(n2)
    E[i], E[j] = n1, n2
    adj[a1].remove(b1)
    adj[a1].append(b2)
    adj[b2].remove(a2)
    adj[b2].append(a1)
    adj[a2].remove(b2)
    adj[a2].append(b1)
    adj[b1].remove(a1)
    adj[b1].append(a2)


def _attempt(s, d, D, deadline, rng):
    """Try to find a bipartite d-regular graph with sides of size s and diameter <= D. Returns edges or None."""
    E, eset, adj = _initial(s, d)
    m = len(E)
    for _ in range(4 * m):
        i, j = rng.randrange(m), rng.randrange(m)
        if i != j and _ok(E, eset, i, j):
            _switch(E, eset, adj, i, j)
    N = 2 * s
    cur = _cost(adj, N, D)
    T = 2.0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        i, j = rng.randrange(m), rng.randrange(m)
        if i == j or not _ok(E, eset, i, j):
            continue
        _switch(E, eset, adj, i, j)
        c = _cost(adj, N, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            _switch(E, eset, adj, i, j)
    return [(a, b) for a, b in E]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline_all = t0 + 0.8 * time_limit
    rng = random.Random(seed)
    best = None
    for s in (300, 340, 350, 360, 370, 385):
        remaining = deadline_all - time.monotonic()
        if remaining <= 1.0:
            break
        dl = time.monotonic() + max(1.0, 0.5 * remaining)
        try:
            edges = _attempt(s, d, D, dl, rng)
        except Exception:
            break
        if edges is None:
            break
        n = 2 * s
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
        else:
            break
    return best if best is not None else trivial(d, D)
