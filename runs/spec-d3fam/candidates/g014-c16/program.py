import math
import random
import time

import lib


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
    """Ordered count of vertex pairs at distance > D (bitmask BFS)."""
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


def _star_cover(n, adj, col, deg, d, need_col, rng):
    """NEW HELPER: find a 'star' cover. Look for a vertex w of colour need_col whose whole
    neighbourhood S = N(w) has spare degree and whose neighbourhoods jointly reach every
    vertex of colour need_col. Returns sorted S, or None.

    Used to attach a new vertex X of colour 1-need_col with neighbourhood S: X then sits at
    distance 2 from every vertex of colour need_col.
    """
    need = [v for v in range(n) if col[v] == need_col]
    needset = set(need)
    rng.shuffle(need)
    for w in need:
        S = adj[w]
        if not S or len(S) > d - 1:
            continue
        if any(deg[y] >= d for y in S):
            continue
        cov = set()
        for y in S:
            cov |= adj[y]
        if needset <= cov:
            return sorted(S)
    return None


def _cover_extend(n, edges, d, D, rng):
    """NEW HELPER: add two vertices P and L with degree <= d by star covers, then
    verify the result. P gets the neighbourhood of a vertex w (colour 1) and L the
    neighbourhood of a vertex z (colour 0), and P-L is joined. Returns (n+2, edges) or None.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)
    deg = [len(a) for a in adj]

    SP = _star_cover(n, adj, col, deg, d, 1, rng)   # P has colour 1, neighbours colour 0
    if SP is None:
        return None
    SL = _star_cover(n, adj, col, deg, d, 0, rng)   # L has colour 0, neighbours colour 1
    if SL is None:
        return None

    P, L = n, n + 1
    new = list(edges)
    new.extend((y, P) for y in SP)
    new.extend((z, L) for z in SL)
    new.append((L, P))
    if lib.is_valid(n + 2, new, d, D):
        return n + 2, new
    return None


def _augment(n, edges, d, D, rng, deadline):
    """Add two new vertices (a point P and a line L) using degree-preserving edge switches,
    then anneal with 2-switches minimising pairs at distance > D.
    Returns (n+2, edges) with diameter <= D, or None if the search fails before the deadline.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
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
    T = 1.0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new = _bad_count(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return N, list(E)


def _haar_fallback(d, D, rng, deadline):
    """Random Haar graphs (parent approach); always returns a valid graph."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if D != 3:
        return _haar_fallback(d, D, rng, deadline)

    # Candidate structured bases for D = 3.
    cands = []
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        cands.append(lib.projective_plane_incidence(q))          # degree d, order 2(q^2+q+1)
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        cands.append(lib.araujo_lopez_graph(d - 2))              # degree d, record order
        cands.append(lib.projective_plane_incidence(d - 2))      # degree d-1 with spare degree

    best = None
    for n0, e0 in cands:
        if not lib.is_valid(n0, e0, d, D):
            continue
        cur = (n0, e0)
        # New helper: grow by star covers while they succeed.
        while time.monotonic() < deadline:
            res = _cover_extend(cur[0], cur[1], d, D, rng)
            if res is None:
                break
            cur = res
        if best is None or cur[0] > best[0]:
            best = cur

    if best is None:
        return _haar_fallback(d, D, rng, deadline)

    # Grow further by annealing switches from the best base.
    mb = _moore(d, D)
    cur = best
    while time.monotonic() < deadline and cur[0] + 2 <= mb:
        res = _cover_extend(cur[0], cur[1], d, D, rng)
        if res is None:
            res = _augment(cur[0], cur[1], d, D, rng, deadline)
        if res is None or not lib.is_valid(res[0], res[1], d, D):
            break
        cur = res

    if lib.is_valid(cur[0], cur[1], d, D):
        return cur
    return _haar_fallback(d, D, rng, start + time_limit * 0.9)
