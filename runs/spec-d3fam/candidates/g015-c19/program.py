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


def _bad_total(reach, N):
    """Ordered number of pairs at distance > D."""
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


def _try_switch(adj, col, p, b, q, e):
    """Check that the 2-switch (p,b),(q,e) -> (p,e),(q,b) keeps a simple bipartite graph.

    Returns True if the switch is legal. Degrees are preserved by any switch.
    """
    if p == e or b == q or p == q or b == e:
        return False
    if e in adj[p] or b in adj[q]:
        return False
    if col[p] == col[e] or col[q] == col[b]:
        return False
    return True


def _apply(adj, p, b, q, e, forward):
    """Forward: remove (p,b),(q,e), add (p,e),(q,b). Backward: the reverse."""
    if forward:
        r1, r2, a1, a2 = (p, b), (q, e), (p, e), (q, b)
    else:
        r1, r2, a1, a2 = (p, e), (q, b), (p, b), (q, e)
    for x, y in (r1, r2):
        adj[x].discard(y)
        adj[y].discard(x)
    for x, y in (a1, a2):
        adj[x].add(y)
        adj[y].add(x)


def _propose_targeted(N, adj, col, reach, rng):
    """Propose a 2-switch that tries to bring a bad pair (x, y) closer.

    Pick a bad pair (x, y). Pick p near x and e near y with the right colour, so the new edge
    (p, e) shortens the x-y route. Then pick the other two edges at random.
    """
    full = (1 << N) - 1
    cand = [v for v in range(N) if reach[v] != full]
    if not cand:
        return None
    x = rng.choice(cand)
    miss = full & ~reach[x]
    ys = [i for i in range(N) if (miss >> i) & 1]
    y = rng.choice(ys)
    if not adj[x] or not adj[y]:
        return None
    if col[x] != col[y]:
        e = rng.choice(list(adj[y]))
    else:
        mid = rng.choice(list(adj[y]))
        if not adj[mid]:
            return None
        e = rng.choice(list(adj[mid]))
        if e == y:
            return None
    p = rng.choice(list(adj[x]))
    if not adj[p] or not adj[e]:
        return None
    b = rng.choice(list(adj[p]))
    q = rng.choice(list(adj[e]))
    return p, b, q, e


def _propose_random(N, adj, col, rng):
    """Propose an unbiased random 2-switch."""
    p = rng.randrange(N)
    e = rng.randrange(N)
    if not adj[p] or not adj[e] or col[p] == col[e]:
        return None
    b = rng.choice(list(adj[p]))
    q = rng.choice(list(adj[e]))
    return p, b, q, e


def _augment(n, edges, d, D, rng, deadline):
    """Add two new vertices (a point P and a line L) using degree-preserving edge switches.

    Setup: take a matching of d edges (a_i, b_i) and replace each by (a_i, P) and (b_i, L).
    Degrees of old vertices are unchanged; P and L get degree d.
    Search: targeted 2-switches aimed at bad pairs, mixed with random switches, with
    Metropolis acceptance on the number of pairs at distance > D.
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

    reach = _reach(N, adj, D)
    cur = _bad_total(reach, N)
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        if rng.random() < 0.8:
            prop = _propose_targeted(N, adj, col, reach, rng)
        else:
            prop = _propose_random(N, adj, col, rng)
        if prop is None:
            continue
        p, b, q, e = prop
        if not _try_switch(adj, col, p, b, q, e):
            continue
        _apply(adj, p, b, q, e, True)
        new_reach = _reach(N, adj, D)
        new = _bad_total(new_reach, N)
        T = max(0.2, 1.0 - (time.monotonic() - deadline) / 1e9 * 0 - 0.0)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            reach = new_reach
        else:
            _apply(adj, p, b, q, e, False)

    out = []
    for u in range(N):
        for v in adj[u]:
            if u < v:
                out.append((u, v))
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
