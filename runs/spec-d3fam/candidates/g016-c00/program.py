import math
import random
import time

import lib


def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency sets (DFS from each unseen vertex)."""
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


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


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


def _bad_from_reach(N, reach):
    """Ordered count of pairs at distance > D, from reach masks."""
    return sum(N - r.bit_count() for r in reach)


def _find(E, u, v):
    """Index of the edge {u, v} in the edge list E (either orientation)."""
    try:
        return E.index((u, v))
    except ValueError:
        return E.index((v, u))


def _two_switch(adj, E, p, q, r, s):
    """Replace edges (p,q),(r,s) by (p,s),(r,q). Degrees are preserved; E is updated in place."""
    i = _find(E, p, q)
    j = _find(E, r, s)
    adj[p].discard(q)
    adj[q].discard(p)
    adj[r].discard(s)
    adj[s].discard(r)
    adj[p].add(s)
    adj[s].add(p)
    adj[r].add(q)
    adj[q].add(r)
    E[i] = (p, s)
    E[j] = (r, q)


def _random_proposal(adj, E, rng):
    """Uniformly random 2-switch proposal (a,b),(c,e) -> (a,e),(c,b) as (p,q,r,s)."""
    M = len(E)
    i = rng.randrange(M)
    j = rng.randrange(M)
    if i == j:
        return None
    a, b = E[i]
    c, e = E[j]
    if a == c or b == e or e in adj[a] or b in adj[c]:
        return None
    return (a, b, c, e)


def _focused_proposal(N, adj, reach, col, full, rng):
    """Guided 2-switch aimed at a bad pair (x, y).

    Picks x that still has a vertex y of opposite colour at distance > D. Then
    p = colour-0 end, s = colour-1 end, and q a neighbour of p, r a neighbour of s.
    The switch (p,q),(r,s) -> (p,s),(r,q) makes p and s adjacent, which
    directly shortens the bad pair.
    """
    cands = [v for v in range(N) if reach[v] != full]
    if not cands:
        return None
    x = rng.choice(cands)
    opp = 0
    for v in range(N):
        if col[v] != col[x]:
            opp |= 1 << v
    missing = (full ^ reach[x]) & opp
    if not missing:
        return None
    bits = [y for y in range(N) if (missing >> y) & 1]
    y = rng.choice(bits)
    if col[x] == 0:
        p, s = x, y
    else:
        p, s = y, x
    q = rng.choice(list(adj[p]))
    r = rng.choice(list(adj[s]))
    if q in adj[r]:
        return None
    return (p, q, r, s)


def _augment(n, edges, d, D, rng, deadline):
    """Add two new vertices (a point P and a line L) and anneal with degree-preserving 2-switches.

    Step 1: pick a matching of d edges (a_i, b_i); replace each by (a_i, P) and (b_i, L).
    Step 2: anneal with a mix of random and focused 2-switches, minimising pairs at distance > D.
    Returns (n+2, edges) with diameter <= D, or None if the search fails before the deadline.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1                      # P has colour 1 (neighbours colour 0); L has colour 0
    adj.append(set())
    adj.append(set())
    col.append(1)
    col.append(0)
    N = n + 2
    full = (1 << N) - 1

    oriented = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]  # (colour0, colour1)
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

    picked = set(pick)
    E = [oriented[i] for i in range(len(oriented)) if i not in picked]
    for idx in pick:
        a, b = oriented[idx]
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(P)
        adj[P].add(a)
        adj[b].add(L)
        adj[L].add(b)
        E.append((a, P))
        E.append((L, b))

    reach = _reach(N, adj, D)
    cur = _bad_from_reach(N, reach)
    T = 1.0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        if rng.random() < 0.6:
            move = _focused_proposal(N, adj, reach, col, full, rng)
        else:
            move = _random_proposal(adj, E, rng)
        if move is None:
            continue
        p, q, r, s = move
        _two_switch(adj, E, p, q, r, s)
        new_reach = _reach(N, adj, D)
        new = _bad_from_reach(N, new_reach)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            reach = new_reach
        else:
            # Revert: (p,s),(r,q) -> (p,q),(r,s)
            _two_switch(adj, E, p, s, r, q)
    return N, list(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    # Structured bases for D = 3.
    base = None
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        base = lib.projective_plane_incidence(q)          # order 2(q^2+q+1), degree q+1
    elif D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        base = lib.araujo_lopez_graph(d - 2)              # order 2(q^2+q+5), degree q+2 = d

    if base is not None:
        n, edges = base
        if lib.is_valid(n, edges, d, D):
            cur = (n, edges)
            mb = _moore(d, D)
            # Repeatedly try to grow by two vertices while time and the Moore bound allow.
            while time.monotonic() < deadline and cur[0] + 2 <= mb:
                res = _augment(cur[0], cur[1], d, D, rng, deadline)
                if res is None:
                    break
                if not lib.is_valid(res[0], res[1], d, D):
                    break
                cur = res
            return cur

    # Fallback: random Haar graphs.
    best = lib.haar_graph(d, range(d))          # complete bipartite K_{d,d}: always valid
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
