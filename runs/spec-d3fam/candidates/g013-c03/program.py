import math
import random
import time

import lib


def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency collections (iterative DFS from each unseen vertex)."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _reach(N, adj, D):
    """Per-vertex bitmask of vertices within distance D."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _bad(N, reach):
    """Ordered count of vertex pairs at distance greater than D."""
    return sum(N - r.bit_count() for r in reach)


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _check(adj, col, rem, add):
    """Accept a 2-switch only if it is non-degenerate and every new edge joins opposite colours."""
    if len({frozenset(e) for e in rem}) < 2:
        return None
    if len({frozenset(e) for e in add}) < 2:
        return None
    for u, v in add:
        if u == v or v in adj[u] or col[u] == col[v]:
            return None
    return rem, add


def _targeted_move(N, adj, col, reach, rng):
    """Directed repair move for a bad pair (x, y).

    If col[x] != col[y]: switch (x,a),(c,y) -> (x,y),(a,c) with a in N(x), c in N(y),
    which creates the edge x-y (distance 1).
    If col[x] == col[y]: switch (x,a),(c,y) -> (x,c),(a,y), which creates the
    path x-c-y (distance 2). Degrees are preserved either way.
    """
    full = (1 << N) - 1
    bad_x = [x for x in range(N) if reach[x] != full]
    if not bad_x:
        return None
    x = rng.choice(bad_x)
    miss = full ^ reach[x]
    ys = [y for y in range(N) if (miss >> y) & 1]
    y = rng.choice(ys)
    if not adj[x] or not adj[y]:
        return None
    a = rng.choice(list(adj[x]))
    c = rng.choice(list(adj[y]))
    rem = [(x, a), (c, y)]
    if col[x] != col[y]:
        add = [(x, y), (a, c)]
    else:
        add = [(x, c), (a, y)]
    return _check(adj, col, rem, add)


def _random_move(N, adj, col, rng):
    """Ordinary random 2-switch, used for diversification."""
    x = rng.randrange(N)
    if not adj[x]:
        return None
    a = rng.choice(list(adj[x]))
    c = rng.randrange(N)
    if not adj[c]:
        return None
    e = rng.choice(list(adj[c]))
    rem = [(x, a), (c, e)]
    add = [(x, e), (c, a)]
    return _check(adj, col, rem, add)


def _apply(adj, rem, add):
    for u, v in rem:
        adj[u].discard(v)
        adj[v].discard(u)
    for u, v in add:
        adj[u].add(v)
        adj[v].add(u)


def _undo(adj, rem, add):
    for u, v in add:
        adj[u].discard(v)
        adj[v].discard(u)
    for u, v in rem:
        adj[u].add(v)
        adj[v].add(u)


def _augment(n, edges, col0, d, D, rng, deadline):
    """Add a point P (colour 1) and a line L (colour 0) to a bipartite d-regular graph.

    Step 1: pick a matching of d edges (a_i, b_i) with a_i colour 0; replace each by
            (a_i, P) and (b_i, L). All old degrees are unchanged; P and L get degree d.
    Step 2: anneal with degree-preserving 2-switches, mostly the targeted moves
            that directly repair a chosen bad pair, minimising pairs at distance > D.
    Returns (N, edges) with diameter <= D, or None if the search fails before the deadline.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = list(col0)

    P, L = n, n + 1
    adj.append(set())
    adj.append(set())
    col.append(1)
    col.append(0)
    N = n + 2

    oriented = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]
    rng.shuffle(oriented)
    used, pick = set(), []
    for idx, (a, b) in enumerate(oriented):
        if a not in used and b not in used:
            pick.append(idx)
            used.add(a)
            used.add(b)
            if len(pick) == d:
                break
    if len(pick) < d:
        return None

    for idx in pick:
        a, b = oriented[idx]
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(P)
        adj[P].add(a)
        adj[b].add(L)
        adj[L].add(b)

    reach = _reach(N, adj, D)
    cur = _bad(N, reach)
    T = 0.6
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        if rng.random() < 0.85:
            mv = _targeted_move(N, adj, col, reach, rng)
        else:
            mv = _random_move(N, adj, col, rng)
        T = max(0.05, T * 0.9995)
        if mv is None:
            continue
        rem, add = mv
        _apply(adj, rem, add)
        new_reach = _reach(N, adj, D)
        new = _bad(N, new_reach)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            reach = new_reach
        else:
            _undo(adj, rem, add)

    out = [(u, v) for u in range(N) for v in adj[u] if u < v]
    return N, out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    base = None
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        base = lib.projective_plane_incidence(q)          # order 2(q^2+q+1), degree q+1
    elif D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        base = lib.araujo_lopez_graph(d - 2)              # order 2(q^2+q+5), degree q+2 = d

    if base is not None:
        n, edges = base
        if lib.is_valid(n, edges, d, D):
            col = _color(n, lib.adjacency(n, edges))
            cur = (n, edges)
            mb = _moore(d, D)
            while time.monotonic() < deadline and cur[0] + 2 <= mb:
                res = _augment(cur[0], cur[1], col, d, D, rng, deadline)
                if res is None:
                    break
                if not lib.is_valid(res[0], res[1], d, D):
                    break
                cur = res
                col = col + [1, 0]
            return cur

    # Fallback: random Haar graphs.
    best = lib.haar_graph(d, range(d))          # K_{d,d}: always valid
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best
