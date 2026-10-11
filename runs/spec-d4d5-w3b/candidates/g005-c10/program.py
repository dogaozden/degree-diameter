import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Growing edge-switch annealing for bipartite d-regular graphs.
#
# State: a d-regular bipartite graph on N + N vertices, stored as a list of
# edges (a, b) with a, b in 0..N-1 (A side and B side). Vertex ids in the
# adjacency structure are a for A-side and N + b for B-side.
#
# Moves: degree-preserving edge switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
# Cost: number of ordered vertex pairs at distance > D (zero means valid).
#
# Growth: add one A vertex and one B vertex, each of degree d, by subdividing
# d edges with pairwise-disjoint endpoints. The previous solution is kept as
# the starting point, so the search climbs N one step at a time.
# ----------------------------------------------------------------------------


def _moore_per_side(d, D):
    return sum((d - 1) ** i for i in range(D))


def _cost(adj, n, D):
    """Number of ordered vertex pairs not within distance D. Zero means diameter <= D."""
    full = (1 << n) - 1
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
        if all(r == full for r in reach):
            return 0
    return sum(n - r.bit_count() for r in reach)


def _random_regular(N, d, rng):
    """Union of d random disjoint perfect matchings between A and B; returns (E, S) or None."""
    for _ in range(50):
        S = set()
        E = []
        ok = True
        for _layer in range(d):
            found = None
            for _t in range(300):
                p = list(range(N))
                rng.shuffle(p)
                if all((a, p[a]) not in S for a in range(N)):
                    found = p
                    break
            if found is None:
                ok = False
                break
            for a in range(N):
                S.add((a, found[a]))
                E.append((a, found[a]))
        if ok:
            return E, S
    return None


def _make_adj(N, E):
    adj = [[] for _ in range(2 * N)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    return adj


def _swap_nb(adj, v, old, new):
    lst = adj[v]
    lst[lst.index(old)] = new


def _switch(adj, N, a1, b1, a2, b2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1) in the adjacency structure."""
    _swap_nb(adj, a1, N + b1, N + b2)
    _swap_nb(adj, N + b1, a1, a2)
    _swap_nb(adj, a2, N + b2, N + b1)
    _swap_nb(adj, N + b2, a2, a1)


def _grow(N, E, d, rng):
    """Add one A vertex N and one B vertex N, each of degree d, by subdividing d disjoint edges."""
    idx = list(range(len(E)))
    rng.shuffle(idx)
    usedA, usedB = set(), set()
    chosen = []
    for i in idx:
        a, b = E[i]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        chosen.append(i)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    cs = set(chosen)
    newE = [E[k] for k in range(len(E)) if k not in cs]
    for i in chosen:
        a, b = E[i]
        newE.append((a, N))  # a joined to new B vertex N
        newE.append((N, b))  # new A vertex N joined to b
    return N + 1, newE


def _anneal(N, E, d, D, deadline, rng):
    """Edge-switch annealing at fixed N. Returns a valid edge list (pairs) or None."""
    n = 2 * N
    E = [[a, b] for a, b in E]
    adj = _make_adj(N, E)
    S = {(a, b) for a, b in E}
    c = _cost(adj, n, D)
    if c == 0:
        return [tuple(e) for e in E]
    c0 = c
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    T0 = max(1.0, 0.03 * c0)
    T_end = 0.3
    m = len(E)
    while c > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - t_start) / span)
        T = T0 * (T_end / T0) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        _switch(adj, N, a1, b1, a2, b2)
        c2 = _cost(adj, n, D)
        delta = c2 - c
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            c = c2
            S.discard((a1, b1))
            S.discard((a2, b2))
            S.add((a1, b2))
            S.add((a2, b1))
            E[i] = [a1, b2]
            E[j] = [a2, b1]
        else:
            _switch(adj, N, a1, b2, a2, b1)
    if c == 0:
        return [tuple(e) for e in E]
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + max(1.0, 0.8 * time_limit)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    rng = random.Random(seed * 1000003 + d * 101 + D)

    init = _random_regular(d, d, rng)
    if init is None:
        return fallback
    cur_N, cur_E = d, init[0]

    res = _anneal(cur_N, cur_E, d, D, end, rng)
    if res is None:
        return fallback
    cur_E = res

    best_N = cur_N
    best_E = [(a, cur_N + b) for a, b in cur_E]

    while time.monotonic() < end:
        now = time.monotonic()
        remaining = end - now
        slice_end = min(end, now + max(1.0, 0.2 * remaining))
        g = _grow(cur_N, cur_E, d, rng)
        if g is None:
            break
        N1, E1 = g
        res = _anneal(N1, E1, d, D, slice_end, rng)
        if res is not None:
            cur_N, cur_E = N1, res
            if N1 > best_N:
                best_N = N1
                best_E = [(a, N1 + b) for a, b in res]

    n = 2 * best_N
    if lib.is_valid(n, best_E, d, D):
        return n, best_E
    return fallback
