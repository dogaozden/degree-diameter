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


def _reach(N, adj, D):
    """Bitmask per vertex of all vertices within distance D."""
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


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _pick_switch(E, N, reach, rng, p_targeted):
    """Choose two edge indices for a 2-switch.

    Invention: bad-pair-directed move selection. With probability p_targeted, pick a random
    pair (x, y) at distance > D and choose the first edge from an edge incident to x or y,
    so the annealer rewires exactly where the defect is. Otherwise choose uniformly.
    """
    M = len(E)
    i = None
    if rng.random() < p_targeted:
        xs = [x for x in range(N) if reach[x].bit_count() < N]
        if xs:
            x = rng.choice(xs)
            rx = reach[x]
            missing = [y for y in range(N) if not (rx >> y) & 1]
            y = rng.choice(missing)
            cand = [k for k, (a, b) in enumerate(E) if a == x or b == x or a == y or b == y]
            if cand:
                i = rng.choice(cand)
    if i is None:
        i = rng.randrange(M)
    j = rng.randrange(M)
    return i, j


def _augment(n, edges, d, D, rng, deadline):
    """Add two new vertices (a point P and a line L) using degree-preserving edge switches.

    Step 1: pick a matching of d edges (a_i, b_i); replace each by (a_i, P) and (b_i, L).
            Degrees of all old vertices are unchanged and P, L get degree d.
    Step 2: anneal with 2-switches (a,b),(c,e) -> (a,e),(c,b), which keep degrees and
            bipartiteness (edges stored as (colour0, colour1)), minimising pairs at distance > D.
            Moves are chosen by bad-pair-directed selection (see _pick_switch).
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

    M = len(E)
    reach = _reach(N, adj, D)
    cur = _bad_from_reach(N, reach)
    T = 0.6
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        i, j = _pick_switch(E, N, reach, rng, 0.7)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        # apply 2-switch: (a,b),(c,e) -> (a,e),(c,b)
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new_reach = _reach(N, adj, D)
        new = _bad_from_reach(N, new_reach)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            reach = new_reach
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return N, list(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
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
            while time.monotonic() < deadline and cur[0] + 2 <= mb:
                res = _augment(cur[0], cur[1], d, D, rng, deadline)
                if res is None:
                    break
                if not lib.is_valid(res[0], res[1], d, D):
                    break
                cur = res
            if lib.is_valid(cur[0], cur[1], d, D):
                return cur
            return base

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
