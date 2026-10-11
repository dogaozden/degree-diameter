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


def _saturate(n, edges, d, rng):
    """Add opposite-side edges between deficient vertices. Never hurts the diameter."""
    edges = [tuple(e) for e in edges]
    adj = _adj_sets(n, edges)
    deg = [len(a) for a in adj]
    col = _color(n, adj)
    left = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d and b not in adj[a]:
            edges.append((a, b))
            adj[a].add(b)
            adj[b].add(a)
            deg[a] += 1
            deg[b] += 1
    return edges


def _augment(n, edges, d, D, rng, deadline, iters):
    """Add two vertices P (colour 1) and L (colour 0) keeping every old degree fixed.

    A matching of d edges (a_i, b_i) is replaced by (a_i, P) and (b_i, L), so P and L
    get degree d. Then anneal with bipartite-preserving 2-switches
    (a,b),(c,e) -> (a,e),(c,b) to minimise the number of pairs at distance > D.
    Returns (n+2, edges) with zero bad pairs, or None.
    """
    adj = _adj_sets(n, edges)
    col = _color(n, adj)
    P, L = n, n + 1
    adj.append(set())
    adj.append(set())
    N = n + 2

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

    M = len(E)
    cur = _bad_count(N, adj, D)
    for t in range(iters):
        if cur == 0:
            break
        if (t & 31) == 0 and time.monotonic() >= deadline:
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
        T = max(0.3, 1.2 - 0.9 * t / max(1, iters))
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
    if cur != 0:
        return None
    return N, [tuple(x) for x in E]


def _search_haar(d, D, rng, deadline):
    """Random Haar-graph search over Z_m for m increasing; returns the best valid graph found."""
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
        if found:
            if found[0] > best[0]:
                best = found
            misses = 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        # Structured regular bases of degree d with diameter 3.
        bases = []
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            bases.append(lib.projective_plane_incidence(d - 1))   # degree q+1 = d
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                bases.append(lib.araujo_lopez_graph(d - 2))       # degree q+2 = d, record order
            except ValueError:
                pass
        valid = [b for b in bases if lib.is_valid(b[0], b[1], d, D)]
        for n, e in valid:
            consider(n, e)

        if valid:
            n0, e0 = max(valid, key=lambda b: b[0])
            e0 = _saturate(n0, e0, d, rng)
            cur = (n0, e0)
            consider(cur[0], cur[1])
            mb = _moore(d, D)
            # Grow by two vertices at a time while the Moore bound and time allow.
            while time.monotonic() < deadline and cur[0] + 2 <= mb:
                res = _augment(cur[0], cur[1], d, D, rng, deadline, iters=3000)
                if res is not None and lib.is_valid(res[0], res[1], d, D):
                    cur = res
                    consider(cur[0], cur[1])
            return best

    # Fallback for other cases: random Haar search.
    found = _search_haar(d, D, rng, deadline)
    consider(found[0], found[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
