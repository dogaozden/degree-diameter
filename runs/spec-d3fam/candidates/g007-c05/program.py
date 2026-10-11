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


def _bad(reach, N):
    """Ordered count of pairs at distance > D, from reach masks."""
    return sum(N - r.bit_count() for r in reach)


def _swap(adj, a, b, c, e):
    """2-switch: remove (a,b),(c,e); add (a,e),(c,b). Preserves degrees and bipartiteness."""
    adj[a].discard(b); adj[b].discard(a)
    adj[c].discard(e); adj[e].discard(c)
    adj[a].add(e); adj[e].add(a)
    adj[c].add(b); adj[b].add(c)


def _grow(n, edges, d, D, rng, deadline):
    """Add two vertices P (colour 1) and L (colour 0) to a valid bipartite graph.

    Start: a matching of d edges (a_i,b_i) is replaced by (a_i,P), (b_i,L).
    Then anneal with 2-switches minimising bad pairs. Each step is either:
      - TARGETED: pick a vertex x with a bad partner y of opposite colour, then
        switch (a0,b),(c,b1) -> (a0,b1),(c,b) where (a0,b1) = (x,y) is the missing
        pair. This directly attacks a violated distance.
      - RANDOM: a uniform 2-switch (parent move).
    Returns (N, edges) with diameter <= D, or None if the deadline passes.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

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

    colour_mask = [0, 0]
    for v in range(N):
        colour_mask[col[v]] |= 1 << v
    S0 = [v for v in range(N) if col[v] == 0]
    full = (1 << N) - 1

    reach = _reach(N, adj, D)
    cur = _bad(reach, N)
    T = 0.7
    while cur > 0:
        if time.monotonic() >= deadline:
            return None

        move = None
        if rng.random() < 0.5:
            # Targeted move toward a violated opposite-colour pair.
            x = rng.randrange(N)
            miss = full & ~reach[x] & colour_mask[1 - col[x]]
            if miss:
                bits = [i for i in range(N) if (miss >> i) & 1]
                y = rng.choice(bits)
                if col[x] == 0:
                    a0, b1 = x, y
                else:
                    a0, b1 = y, x
                if adj[a0] and adj[b1]:
                    b = rng.choice(list(adj[a0]))
                    c = rng.choice(list(adj[b1]))
                    if c != a0 and b != b1 and b not in adj[c]:
                        move = (a0, b, c, b1)

        if move is None:
            # Uniform random 2-switch.
            a = rng.choice(S0)
            b = rng.choice(list(adj[a]))
            c = rng.choice(S0)
            e = rng.choice(list(adj[c]))
            if a == c or b == e or e in adj[a] or b in adj[c]:
                continue
            move = (a, b, c, e)

        a, b, c, e = move
        _swap(adj, a, b, c, e)
        new_reach = _reach(N, adj, D)
        new = _bad(new_reach, N)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            reach = new_reach
        else:
            _swap(adj, a, e, c, b)  # undo

    out = [(u, v) for u in S0 for v in adj[u]]
    return N, out


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


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
                res = _grow(cur[0], cur[1], d, D, rng, deadline)
                if res is None:
                    break
                if not lib.is_valid(res[0], res[1], d, D):
                    break
                cur = res
            return cur

    # Fallback: random Haar graphs.
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
