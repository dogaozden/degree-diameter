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


def _reach(n, adj, D):
    """Bitmask of vertices within distance D, per vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _structured_base(d, D):
    """Structured starting graph for D = 3, or None."""
    if D != 3:
        return None
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def _attach_pair(n, edges, d, rng):
    """Add a point P and a line L of degree d by moving a matching of d edges onto them.

    Returns (N, E, adj) with E oriented as (colour0, colour1), or None.
    Degrees of old vertices are unchanged.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)
    P, L = n, n + 1
    adj.append(set())
    adj.append(set())

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
    return n + 2, E, adj


def _focused_anneal(N, E, adj, D, rng, deadline):
    """Bad-pair-focused annealing with degree- and bipartiteness-preserving 2-switches.

    Each move picks a vertex x that still has a pair at distance > D, then (usually)
    chooses one of the edges touching x as the first switch edge. This concentrates
    effort where the defects are. The best state seen is tracked.
    Returns the edge list if a zero-defect state was found, else None.
    """
    M = len(E)
    reach = _reach(N, adj, D)
    cur = sum(N - r.bit_count() for r in reach)
    best, bestE = cur, list(E)
    T = 0.7
    while cur > 0 and time.monotonic() < deadline:
        bad = [v for v in range(N) if reach[v].bit_count() < N]
        x = rng.choice(bad)
        inc = [k for k in range(M) if x in E[k]]
        if inc and rng.random() < 0.8:
            i = rng.choice(inc)
        else:
            i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        # 2-switch: (a,b),(c,e) -> (a,e),(c,b)
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new_reach = _reach(N, adj, D)
        new = sum(N - r.bit_count() for r in new_reach)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            reach = new_reach
            E[i] = (a, e)
            E[j] = (c, b)
            if cur < best:
                best, bestE = cur, list(E)
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return bestE if best == 0 else None


def _grow_two(n, edges, d, D, rng, deadline):
    """Try to grow a valid graph by two vertices; return (n+2, edges) or None."""
    att = _attach_pair(n, edges, d, rng)
    if att is None:
        return None
    N, E, adj = att
    res = _focused_anneal(N, E, adj, D, rng, deadline)
    if res is None:
        return None
    return N, list(res)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    base = _structured_base(d, D)
    if base is not None and lib.is_valid(base[0], base[1], d, D):
        cur = base
        mb = _moore(d, D)
        while time.monotonic() < deadline and cur[0] + 2 <= mb:
            res = _grow_two(cur[0], cur[1], d, D, rng, deadline)
            if res is None or not lib.is_valid(res[0], res[1], d, D):
                break
            cur = res
        return cur

    # Fallback: random Haar graphs.
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
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
