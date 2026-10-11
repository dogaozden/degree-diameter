import math
import random
import time

import lib


def _bound(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _cost(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nb = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb.append(x)
        ball = nb
    return sum(n - b.bit_count() for b in ball) // 2


def _anneal(n, adj, edges, eset, D, rng, deadline, iters, T0, T1):
    """Simulated annealing over degree-preserving edge switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).

    Edges are stored as (color0, color1) pairs, so every switch keeps the graph bipartite.
    Modifies adj, edges and eset in place. Returns the final cost (0 means valid diameter).
    """
    cost = _cost(n, adj, D)
    m = len(edges)
    if cost == 0 or m < 2:
        return cost
    for it in range(iters):
        if cost == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters - 1))
        i1 = rng.randrange(m)
        i2 = rng.randrange(m)
        if i1 == i2:
            continue
        a1, b1 = edges[i1]
        a2, b2 = edges[i2]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        adj[a1].remove(b1)
        adj[b1].remove(a1)
        adj[a2].remove(b2)
        adj[b2].remove(a2)
        adj[a1].append(b2)
        adj[b2].append(a1)
        adj[a2].append(b1)
        adj[b1].append(a2)
        new = _cost(n, adj, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
            eset.discard((a1, b1))
            eset.discard((a2, b2))
            eset.add((a1, b2))
            eset.add((a2, b1))
            edges[i1] = (a1, b2)
            edges[i2] = (a2, b1)
        else:
            adj[a1].remove(b2)
            adj[b2].remove(a1)
            adj[a2].remove(b1)
            adj[b1].remove(a2)
            adj[a1].append(b1)
            adj[b1].append(a1)
            adj[a2].append(b2)
            adj[b2].append(a2)
    return cost


def _split(n, adj, edges, eset, d, rng):
    """Add two new vertices (one per side), each of degree d, by splitting a random induced matching of size d.

    Each matched edge (x, y) is replaced by (A, y) and (x, B). Existing degrees are unchanged.
    Returns a fresh copy of the enlarged state, or None if no matching of size d exists.
    """
    m = len(edges)
    order = list(range(m))
    rng.shuffle(order)
    used_a, used_b = set(), set()
    match = []
    for i in order:
        a, b = edges[i]
        if a in used_a or b in used_b:
            continue
        match.append(i)
        used_a.add(a)
        used_b.add(b)
        if len(match) == d:
            break
    if len(match) < d:
        return None
    matched = set(match)
    adj2 = [list(x) for x in adj]
    eset2 = set(eset)
    edges2 = [e for i, e in enumerate(edges) if i not in matched]
    A = n
    B = n + 1
    adj2.append([])
    adj2.append([])
    for i in match:
        x, y = edges[i]
        eset2.discard((x, y))
        adj2[x].remove(y)
        adj2[y].remove(x)
        adj2[A].append(y)
        adj2[y].append(A)
        adj2[B].append(x)
        adj2[x].append(B)
        eset2.add((A, y))
        eset2.add((x, B))
        edges2.append((A, y))
        edges2.append((x, B))
    return n + 2, adj2, edges2, eset2


def _grow(d, D, deadline, rng):
    """Start from K_{d,d} and repeatedly add two vertices, annealing back to diameter <= D after each step.

    Keeps the largest state that was verified to have cost 0. Returns (n, edges).
    """
    n = 2 * d
    adj = [[] for _ in range(n)]
    edges = []
    eset = set()
    for i in range(d):
        for j in range(d):
            a, b = i, d + j
            edges.append((a, b))
            eset.add((a, b))
            adj[a].append(b)
            adj[b].append(a)
    best = (n, list(edges))
    iters = 1500 if D >= 5 else 600
    while time.monotonic() < deadline:
        cand = _split(n, adj, edges, eset, d, rng)
        if cand is None:
            break
        n2, adj2, e2, es2 = cand
        cost = _anneal(n2, adj2, e2, es2, D, rng, deadline, iters, 1.0, 0.15)
        if cost == 0:
            n, adj, edges, eset = n2, adj2, e2, es2
            best = (n, list(edges))
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        if D == 2:
            return best

        # Projective plane incidence graph (diameter 3) when d-1 is a prime power.
        q = d - 1
        if D >= 3 and q >= 2 and lib.is_prime_power(q):
            pg = lib.projective_plane_incidence(q)
            consider(pg[0], pg[1])

        if best_n >= _bound(d, D):
            return best

        # Main search: grow from K_{d,d} by vertex-pair splitting with annealed edge switches.
        if d >= 3:
            rng = random.Random(seed * 1000003 + 17 * d + D)
            n, e = _grow(d, D, deadline, rng)
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
