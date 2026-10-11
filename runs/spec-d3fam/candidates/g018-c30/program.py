import math
import random
import time

import lib


def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency collections (DFS from each unseen vertex)."""
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
    """Ordered count of vertex pairs at distance > D (bitmask BFS over adjacency sets)."""
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


def _augment(n, edges, d, D, rng, deadline, max_iters):
    """Add two vertices (a point P and a line L) by degree-preserving 2-switches.

    Step 1: pick a matching of d edges (a_i, b_i) with a_i on colour 0 and b_i on colour 1;
            replace each by (a_i, P) and (b_i, L). Old degrees are unchanged; P and L get degree d.
    Step 2: anneal with 2-switches (a,b),(c,e) -> (a,e),(c,b), which keep degrees and
            bipartiteness, minimising the number of pairs at distance > D.
    Returns (n+2, edges) with diameter <= D, or None on failure or after max_iters.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1          # P has colour 1 (neighbours colour 0); L has colour 0
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
    T = 0.7
    it = 0
    while cur > 0:
        it += 1
        if it > max_iters or time.monotonic() >= deadline:
            return None
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


def _bases(d, D):
    """Structured starting graphs for D = 3: PG(2,d-1), Araujo-Pardo-Lopez, and largest PG below."""
    out = []
    if D != 3:
        return out
    builders = []
    if d - 1 >= 2 and lib.is_prime_power(d - 1):
        builders.append(lambda: lib.projective_plane_incidence(d - 1))
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        builders.append(lambda: lib.araujo_lopez_graph(d - 2))
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            builders.append(lambda q=q: lib.projective_plane_incidence(q))
            break
    for make in builders:
        try:
            n, e = make()
        except (ValueError, AssertionError):
            continue
        if lib.is_valid(n, e, d, D):
            out.append((n, e))
    return out


def _haar_fallback(d, D, deadline, rng):
    """Random Haar graphs for generic (d, D); used when no structured base applies."""
    best = lib.haar_graph(d, range(d))
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
        if found and found[0] > best[0] and lib.is_valid(found[0], found[1], d, D):
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 0:
        return 1, []
    if D == 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    bases = _bases(d, D)
    if not bases:
        return _haar_fallback(d, D, deadline, rng) if D >= 3 else fallback

    cur = max(bases, key=lambda g: g[0])
    if not lib.is_valid(cur[0], cur[1], d, D):
        return fallback

    mb = _moore(d, D)
    misses = 0
    while time.monotonic() < deadline and cur[0] + 2 <= mb and misses < 30:
        res = _augment(cur[0], cur[1], d, D, rng, deadline, max_iters=4000)
        if res is None or not lib.is_valid(res[0], res[1], d, D):
            misses += 1
            continue
        cur = res
        misses = 0

    if lib.is_valid(cur[0], cur[1], d, D):
        return cur
    return fallback
