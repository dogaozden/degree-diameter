import random
import time

import lib


def _adjacency_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _two_colour(n, adj):
    """Return a proper 2-colouring as a list, or None if the graph is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _extend(n, edges, d, D, deadline, rng):
    """Greedily add new vertices, each joined only to deficient (degree < d) vertices of the
    opposite side. A new vertex is kept only if the graph stays valid (bipartite, max degree d,
    diameter <= D). Returns the enlarged (n, edges)."""
    edges = list(edges)
    adj = _adjacency_sets(n, edges)
    color = _two_colour(n, adj)
    if color is None:
        return n, edges
    while time.monotonic() < deadline:
        deficient = [v for v in range(n) if len(adj[v]) < d]
        if not deficient:
            break
        s = rng.randrange(2)
        cand = [v for v in deficient if color[v] == 1 - s]
        if not cand:
            continue
        if rng.random() < 0.5:
            k = min(d, len(cand))
        else:
            k = rng.randint(1, min(d, len(cand)))
        nbrs = rng.sample(cand, k)
        new_edges = [(v, n) for v in nbrs]
        if lib.within_diameter(n + 1, edges + new_edges, D):
            for v in nbrs:
                adj[v].add(n)
            adj.append(set(nbrs))
            color.append(s)
            edges.extend(new_edges)
            n += 1
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    base = None
    if D == 3:
        # Araujo-Pardo & Lopez record family: degree q+2 = d with q = d-2 a prime power.
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                cand = lib.araujo_lopez_graph(q)
                if lib.is_valid(cand[0], cand[1], d, D):
                    base = cand
            except Exception:
                base = None
        # Projective plane incidence graph when d-1 is a prime power.
        if base is None and lib.is_prime_power(d - 1):
            cand = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(cand[0], cand[1], d, D):
                base = cand

    if base is not None:
        n, edges = base
        if D == 3:
            n2, e2 = _extend(n, edges, d, D, deadline, rng)
            if n2 > n and lib.is_valid(n2, e2, d, D):
                return n2, e2
        return base

    # Generic fallback: Haar graph search (cyclic lifts), always valid K_{d,d} as the floor.
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
