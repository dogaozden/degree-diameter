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


def _reach(N, adj, D):
    """Bitmask of all vertices within distance D of each vertex."""
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


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _directed_anneal(N, adj, col, D, rng, deadline):
    """Repair by directed 2-switches, modifying adj in place. Returns True iff no pair is farther than D.

    A switch removes (a,b),(c,e) and adds (a,e),(c,b), with a,c on colour 0 and b,e on colour 1
    so bipartiteness and all degrees are preserved. The move is aimed at a random bad pair
    (x,y): a is x (or a neighbour of x) and e is y (or a neighbour of y), so the new edge (a,e)
    tends to create a short x-y path. Acceptance is Metropolis on the number of bad pairs.
    """
    full = (1 << N) - 1
    reach = _reach(N, adj, D)
    cur = sum(N - r.bit_count() for r in reach)
    T = 0.4
    while cur > 0:
        if time.monotonic() >= deadline:
            return False
        # Pick a random bad pair (x, y).
        while True:
            x = rng.randrange(N)
            if reach[x] != full:
                break
        missing = [v for v in range(N) if not (reach[x] >> v) & 1]
        y = rng.choice(missing)
        # a: colour-0 vertex near x; e: colour-1 vertex near y.
        a = x if col[x] == 0 else rng.choice(list(adj[x]))
        e = y if col[y] == 1 else rng.choice(list(adj[y]))
        if not adj[a] or not adj[e]:
            continue
        b = rng.choice(list(adj[a]))
        c = rng.choice(list(adj[e]))
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        # Apply switch (a,b),(c,e) -> (a,e),(c,b).
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new_reach = _reach(N, adj, D)
        new = sum(N - r.bit_count() for r in new_reach)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur, reach = new, new_reach
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return True


def _augment(n, edges, d, D, rng, deadline):
    """Add two vertices P (colour 1) and L (colour 0) by rewiring a matching of d edges, then repair.

    Returns (n+2, edges) or None.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1
    adj.append(set())
    adj.append(set())
    col = col + [1, 0]
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

    if not _directed_anneal(N, adj, col, D, rng, deadline):
        return None
    out = [(u, v) for u in range(N) for v in adj[u] if u < v]
    return N, out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    base = None
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        base = lib.projective_plane_incidence(q)
    elif D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        base = lib.araujo_lopez_graph(d - 2)

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
            return cur

    # Fallback: K_{d,d} is always valid; try random Haar graphs for larger orders.
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
