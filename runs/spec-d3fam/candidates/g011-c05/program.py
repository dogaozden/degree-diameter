import math
import random
import time

import lib


def _adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _bad_pairs(n, edges, D):
    """Number of unordered pairs at distance > D (unreachable counts)."""
    adj = _adj(n, edges)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _base_graphs(d, D):
    """Candidate valid starting graphs. The first is always K_{d,d} (diameter 2)."""
    cands = [lib.haar_graph(d, range(d))]
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                cands.append(lib.projective_plane_incidence(q))
                break
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                cands.append(lib.araujo_lopez_graph(q))
            except (ValueError, AssertionError):
                pass
    return cands


def _fill_all(n, edges, color, deg, eset, d, rng):
    """Greedily add every possible edge between deficient opposite-side vertices."""
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (a, b) not in eset]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d and (a, b) not in eset:
            edges.append((a, b))
            eset.add((a, b))
            deg[a] += 1
            deg[b] += 1


def _fill_one(n, edges, color, deg, eset, d, rng):
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    if not left or not right:
        return False
    for _ in range(40):
        a = rng.choice(left)
        b = rng.choice(right)
        if (a, b) not in eset:
            edges.append((a, b))
            eset.add((a, b))
            deg[a] += 1
            deg[b] += 1
            return True
    return False


def _propose_switch(edges, eset, rng):
    """Degree-preserving 2-switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1)."""
    m = len(edges)
    i = rng.randrange(m)
    j = rng.randrange(m)
    if i == j:
        return None
    a1, b1 = edges[i]
    a2, b2 = edges[j]
    n1 = (a1, b2)
    n2 = (a2, b1)
    if n1 in eset or n2 in eset:
        return None
    return [(i, edges[i], n1), (j, edges[j], n2)], []


def _propose_slide(n, edges, color, deg, eset, d, rng):
    """Move an edge endpoint: take a deficient x, re-aim edge (y,z) to (x,y); z loses one degree."""
    defi = [v for v in range(n) if deg[v] < d]
    if not defi:
        return None
    x = rng.choice(defi)
    i = rng.randrange(len(edges))
    e0, e1 = edges[i]
    if color[x] == 0:
        new = (x, e1)
        z = e0
    else:
        new = (e0, x)
        z = e1
    if new in eset:
        return None
    return [(i, edges[i], new)], [(x, 1), (z, -1)]


def _apply(edges, eset, deg, changes, dd, forward):
    if forward:
        for _, old, _new in changes:
            eset.discard(old)
        for i, _old, new in changes:
            eset.add(new)
            edges[i] = new
        for v, dl in dd:
            deg[v] += dl
    else:
        for _, _old, new in changes:
            eset.discard(new)
        for i, old, _new in changes:
            eset.add(old)
            edges[i] = old
        for v, dl in dd:
            deg[v] -= dl


def _try_grow(n, edges, color, deg, d, D, rng, deadline, iters):
    """Add two vertices (one per side) and search for edges making the graph diameter <= D.

    Returns (n, edges, color, deg) on success, else None. Input is not mutated.
    """
    n = n + 2
    color = list(color) + [0, 1]
    deg = list(deg) + [0, 0]
    edges = list(edges)
    eset = set(edges)
    _fill_all(n, edges, color, deg, eset, d, rng)
    cost = _bad_pairs(n, edges, D)
    T0 = max(1.0, 0.01 * cost)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (0.02 ** (it / iters))
        if rng.random() < 0.15:
            if _fill_one(n, edges, color, deg, eset, d, rng):
                cost = _bad_pairs(n, edges, D)
            continue
        if rng.random() < 0.55:
            mv = _propose_switch(edges, eset, rng)
        else:
            mv = _propose_slide(n, edges, color, deg, eset, d, rng)
        if mv is None:
            continue
        changes, dd = mv
        _apply(edges, eset, deg, changes, dd, True)
        c2 = _bad_pairs(n, edges, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _apply(edges, eset, deg, changes, dd, False)

    if cost != 0:
        return None
    return n, edges, color, deg


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)

    # Safe fallback: the largest valid starting graph.
    best = None
    for n0, e0 in _base_graphs(d, D):
        if best is not None and n0 <= best[0]:
            continue
        if lib.is_valid(n0, e0, d, D):
            best = (n0, list(e0))
    if best is None:
        return 2, [(0, 1)]

    n0, e0 = best
    adj = _adj(n0, e0)
    color = _bipartition(n0, adj)
    if color is None:
        return best[0], [(u, v) for u, v in best[1]]
    edges = [(u, v) if color[u] == 0 else (v, u) for u, v in e0]
    deg = [len(a) for a in adj]
    state = (n0, edges, color, deg)

    # Bold search: grow from the current valid graph by two vertices at a time,
    # re-wiring with annealed switches, slides and fills until diameter <= D again.
    while time.monotonic() < deadline:
        n, e, c, dg = state
        res = _try_grow(n, e, c, dg, d, D, rng, deadline, 1500)
        if res is None:
            continue
        n2, e2, c2, dg2 = res
        pairs = [(u, v) for u, v in e2]
        if lib.is_valid(n2, pairs, d, D):
            state = res
            best = (n2, pairs)

    out_n, out_e = best
    if not lib.is_valid(out_n, out_e, d, D):
        fb = lib.haar_graph(d, range(d))
        return fb[0], list(fb[1])
    return out_n, [(int(u), int(v)) for u, v in out_e]
