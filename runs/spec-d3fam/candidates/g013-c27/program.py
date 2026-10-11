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


def _bad_count(n, adj, D):
    """Ordered count of vertex pairs at distance > D (bitmask BFS) from adjacency sets/lists."""
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


def _augment(n, edges, d, D, rng, deadline):
    """Add two new vertices (a point P and a line L) using degree-preserving edge switches.

    Step 1: pick a matching of d edges (a_i, b_i); replace each by (a_i, P) and (b_i, L).
    Step 2: anneal with 2-switches, minimising the number of pairs at distance > D.
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


# ----------------------------------------------------- cyclic Haar annealing

def _haar_adj(m, S):
    """Adjacency lists of the Haar graph H(Z_m, S): a_i ~ b_{i+s} for s in S."""
    adj = [[] for _ in range(2 * m)]
    for i in range(m):
        for s in S:
            j = (i + s) % m
            adj[i].append(m + j)
            adj[m + j].append(i)
    return adj


def _anneal_haar(m, d, D, rng, deadline):
    """Search a connection set S (|S| = d, 0 in S) in Z_m whose Haar graph has diameter <= D.

    Returns S, or None if the deadline passes first.
    """
    if d < 2 or d > m:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    cur = _bad_count(2 * m, _haar_adj(m, S), D)
    T = 2.0
    it = 0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        it += 1
        if it % 3000 == 0:
            T = 2.0  # reheat to escape stagnation
        y = rng.randrange(1, m)
        if y in S:
            continue
        idx = rng.randrange(1, d)
        T_new = S.copy()
        T_new[idx] = y
        new = _bad_count(2 * m, _haar_adj(m, T_new), D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            S, cur = T_new, new
        T = max(0.05, T * 0.9995)
    return S


def _random_haar(d, D, rng, deadline):
    """Fallback: random Haar graphs with growing m (always valid; K_{d,d} is the floor)."""
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
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    struct_deadline = start + 0.45 * time_limit   # structured phase budget
    total_deadline = start + 0.85 * time_limit    # hard search budget
    rng = random.Random(seed)
    mb = _moore(d, D)

    # ---- Phase 1: structured base (parent approach), with safe validation.
    best = None
    base = None
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        base = lib.projective_plane_incidence(q)
    elif D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        base = lib.araujo_lopez_graph(d - 2)

    if base is not None and lib.is_valid(base[0], base[1], d, D):
        cur = base
        while time.monotonic() < struct_deadline and cur[0] + 2 <= mb:
            res = _augment(cur[0], cur[1], d, D, rng, struct_deadline)
            if res is None or not lib.is_valid(res[0], res[1], d, D):
                break
            cur = res
        best = cur
    else:
        best = _random_haar(d, D, rng, struct_deadline)

    # ---- Phase 2: different family, cyclic Haar graphs found by annealing.
    # Only accept strictly larger graphs that pass the full validity check.
    m = best[0] // 2 + 1
    while time.monotonic() < total_deadline and 2 * m <= mb:
        S = _anneal_haar(m, d, D, rng, total_deadline)
        if S is None:
            break
        n, edges = lib.haar_graph(m, S)
        if not lib.is_valid(n, edges, d, D):
            break
        best = (n, edges)
        m += 1

    # Final safety net.
    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
