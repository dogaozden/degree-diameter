import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Edge-switch annealing with incremental bipartite growth.
#
# A d-regular bipartite graph with sides of size a is stored as a list E of
# (i, j) pairs (A-vertex i, B-vertex j). Unified ids: A i -> i, B j -> a + j.
# Growth adds one A vertex x and one B vertex y: remove d edges (i_k, j_k) with
# distinct i_k and j_k, then join x to all j_k and y to all i_k. Degrees stay
# exactly d and the graph stays bipartite. Simulated annealing with double-edge
# switches then tries to reach zero "bad pairs" (pairs at distance > D).
# Every accepted state is valid, and the largest valid one is kept.
# ----------------------------------------------------------------------------


def _fallback(d, D):
    """Always-valid graph: K_{d,d} for D >= 2."""
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _cost(n, adj, D):
    """Number of ordered (source, target) pairs at distance > D. Zero means diameter <= D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _unified(a, E):
    adj = [[] for _ in range(2 * a)]
    for i, j in E:
        adj[i].append(a + j)
        adj[a + j].append(i)
    return adj


def _switch(adj, a, E, S, x, y):
    """Double-edge switch of E[x] = (i1, j1) and E[y] = (i2, j2) into (i1, j2), (i2, j1).

    Applying it twice restores the original graph, so it doubles as the undo.
    """
    i1, j1 = E[x]
    i2, j2 = E[y]
    v1, v2 = a + j1, a + j2
    adj[i1].remove(v1)
    adj[v1].remove(i1)
    adj[i2].remove(v2)
    adj[v2].remove(i2)
    adj[i1].append(v2)
    adj[v2].append(i1)
    adj[i2].append(v1)
    adj[v1].append(i2)
    S.discard((i1, j1))
    S.discard((i2, j2))
    S.add((i1, j2))
    S.add((i2, j1))
    E[x] = (i1, j2)
    E[y] = (i2, j1)


def _repair(a, E, D, rng, deadline, iters):
    """Anneal by edge switches until the graph has diameter <= D. Returns E or None."""
    E = list(E)
    S = set(E)
    adj = _unified(a, E)
    n = 2 * a
    m = len(E)
    cost = _cost(n, adj, D)
    T0 = 1.5
    for it in range(iters):
        if cost == 0:
            break
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        T = max(0.15, T0 * (1.0 - it / iters))
        x = rng.randrange(m)
        y = rng.randrange(m)
        if x == y:
            continue
        i1, j1 = E[x]
        i2, j2 = E[y]
        if i1 == i2 or j1 == j2 or (i1, j2) in S or (i2, j1) in S:
            continue
        _switch(adj, a, E, S, x, y)
        c2 = _cost(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _switch(adj, a, E, S, x, y)
    if cost == 0:
        return E
    return None


def _grow(a, E, d, rng):
    """Add one A vertex and one B vertex, keeping d-regularity. Returns (a + 1, E') or None."""
    idxs = list(range(len(E)))
    rng.shuffle(idxs)
    chosen = []
    used_i, used_j = set(), set()
    for k in idxs:
        i, j = E[k]
        if i in used_i or j in used_j:
            continue
        chosen.append(k)
        used_i.add(i)
        used_j.add(j)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    rem = set(chosen)
    out = [e for k, e in enumerate(E) if k not in rem]
    for k in chosen:
        i, j = E[k]
        out.append((a, j))   # new A vertex a joins the old B vertex j
        out.append((i, a))   # new B vertex a joins the old A vertex i
    return a + 1, out


def _ratchet(d, D, a, E, moore, rng, deadline):
    """Repeatedly grow the best valid graph by one vertex per side and repair it."""
    best_a, best_E = a, list(E)
    iters = 1500
    while time.monotonic() < deadline:
        if 2 * (best_a + 1) > moore:
            break
        g = _grow(best_a, best_E, d, rng)
        if g is None:
            break
        a2, E2 = g
        res = _repair(a2, E2, D, rng, deadline, iters)
        if res is not None:
            best_a, best_E = a2, res
        else:
            iters = min(iters * 2, 40000)
    return best_a, best_E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    best = _fallback(d, D)
    if d < 2 or D < 2:
        return best

    moore = lib.moore_bound(d, D)

    # Base: PG(2, d-1) incidence when d-1 is a prime power (diameter 3, d-regular),
    # otherwise K_{d,d} (diameter 2).
    if D >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        m = n0 // 2
        a0 = m
        E0 = [(u, v - m) for u, v in e0]
    else:
        a0 = d
        E0 = [(i, j) for i in range(d) for j in range(d)]

    a, E = _ratchet(d, D, a0, E0, moore, rng, deadline)

    n = 2 * a
    edges = [(i, a + j) for i, j in E]
    if n > best[0] and lib.is_valid(n, edges, d, D):
        best = (n, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d, D)
    return best
