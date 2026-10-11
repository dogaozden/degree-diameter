import math
import random
import time

import lib


def _adj_sets(n, edges):
    """Adjacency as a list of sets."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency sets."""
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


def _bad_count(n, adj, D):
    """Ordered number of vertex pairs at distance > D (bitmask expansion)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _augment_once(n, edges, d, D, rng, deadline, T0=0.7):
    """Add two vertices (point P, line L) by degree-preserving 2-switches.

    Pick a matching of d edges (a_i, b_i) with a_i on colour 0, b_i on colour 1.
    Replace each by (a_i, P) and (b_i, L): old degrees are unchanged, P and L get degree d.
    Then anneal 2-switches (a,b),(c,e) -> (a,e),(c,b), which keep degrees and bipartiteness,
    minimising the number of ordered pairs at distance > D.
    Returns (n+2, edges) with diameter <= D, or None if not solved before deadline.
    """
    adj = _adj_sets(n, edges)
    col = _color(n, adj)
    P, L = n, n + 1
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
    cur = _bad_count(N, adj, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = T0 * max(0.15, 1.0 - (now - start) / span)
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _bad_count(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return N, list(E)


def _grow_search(n, edges, d, D, rng, deadline):
    """Repeatedly try to add two vertices, with restarts; keeps the last valid graph."""
    cur = (n, list(edges))
    mb = _moore(d, D)
    fails = 0
    while time.monotonic() < deadline and cur[0] + 2 <= mb:
        remaining = deadline - time.monotonic()
        budget = max(1.5, remaining / 3.0)
        sub = min(deadline, time.monotonic() + budget)
        res = _augment_once(cur[0], cur[1], d, D, rng, sub)
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            cur = res
            fails = 0
        else:
            fails += 1
            if fails > 25:
                break
    return cur


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is always valid for D >= 2 (optimal for D = 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D == 3:
        bases = []
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            bases.append(lib.projective_plane_incidence(q))      # order 2(q^2+q+1), degree d
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                bases.append(lib.araujo_lopez_graph(d - 2))      # order 2(q^2+q+5), degree d
            except Exception:
                pass
        bases = [b for b in bases if lib.is_valid(b[0], b[1], d, D)]
        for b in bases:
            consider(b[0], b[1])
        if bases:
            cur = max(bases, key=lambda b: b[0])
            grown = _grow_search(cur[0], cur[1], d, D, rng, deadline)
            consider(grown[0], grown[1])
    else:
        # Random Haar graphs: connection sets in Z_m, hill-free random restarts.
        m, misses = d + 1, 0
        while time.monotonic() < deadline and misses < 10:
            found = None
            for _ in range(30):
                if time.monotonic() >= deadline:
                    break
                if d - 1 > m - 1:
                    break
                S = [0] + rng.sample(range(1, m), d - 1)
                n, edges = lib.haar_graph(m, S)
                if lib.within_diameter(n, edges, D):
                    found = (n, edges)
                    break
            if found:
                consider(found[0], found[1])
                misses = 0
            else:
                misses += 1
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
