import math
import random
import time

import lib


def _bad_pairs_adj(n, adj, D):
    """Count unordered vertex pairs at distance > D, using bitmask balls over adjacency sets."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _two_colour(n, adj):
    """Return a 0/1 colouring of each vertex that is proper on every edge (graph assumed bipartite)."""
    side = [-1] * n
    for s in range(n):
        if side[s] != -1:
            continue
        side[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if side[v] == -1:
                    side[v] = 1 - side[u]
                    stack.append(v)
    return side


def _grow_by_pair(n0, edges0, side, d, D, rng, deadline):
    """Try to add one point p and one line l to a valid bipartite graph.

    Moves used (both keep every old vertex's degree and bipartiteness):
      attach: remove an edge (a,b) and add (p,b) and (a,l); this fills p and l.
      2-switch: replace (a,b),(c,e) by (a,e),(c,b); this reshapes the graph.
    Simulated annealing minimises the number of pairs at distance > D.
    Returns (n0+2, edges) with diameter <= D, or None if the search fails.
    """
    p, l = n0, n0 + 1
    n = n0 + 2
    # Oriented edges (point, line) where side[point] == 0 and side[line] == 1.
    edges = [(u, v) if side[u] == 0 else (v, u) for u, v in edges0]
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)

    # Attach p and l, each with d edges, by splitting existing edges.
    for _ in range(d):
        for _try in range(10000):
            i = rng.randrange(len(edges))
            a, b = edges[i]
            if b in adj[p] or a in adj[l]:
                continue
            adj[a].discard(b)
            adj[b].discard(a)
            edges[i] = (p, b)
            adj[p].add(b)
            adj[b].add(p)
            edges.append((a, l))
            adj[a].add(l)
            adj[l].add(a)
            break
        else:
            return None

    cost = _bad_pairs_adj(n, adj, D)
    m = len(edges)
    T0, T1 = 1.0, 0.05
    t_start = time.monotonic()
    span = max(deadline - t_start, 1e-6)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min((now - t_start) / span, 1.0)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = edges[i]
        c, e = edges[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        # Apply the 2-switch: (a,b),(c,e) -> (a,e),(c,b).
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new_cost = _bad_pairs_adj(n, adj, D)
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            edges[i] = (a, e)
            edges[j] = (c, b)
            cost = new_cost
        else:
            # Revert the 2-switch.
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)

    if cost == 0:
        return n, [(a, b) for a, b in edges]
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    if D == 3:
        # Araujo-Pardo & Lopez record: (q+2)-regular, order 2(q^2+q+5), q = d-2 prime power.
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            n, edges = lib.araujo_lopez_graph(q)
            if lib.is_valid(n, edges, d, D):
                adj = [set() for _ in range(n)]
                for u, v in edges:
                    adj[u].add(v)
                    adj[v].add(u)
                side = _two_colour(n, adj)
                ext = _grow_by_pair(n, edges, side, d, D, rng, deadline)
                if ext is not None:
                    n2, e2 = ext
                    if lib.is_valid(n2, e2, d, D):
                        return n2, e2
                return n, edges
        # Projective plane incidence graph: order 2(q^2+q+1) with q = d-1.
        if lib.is_prime_power(d - 1):
            n, edges = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, edges, d, D):
                return n, edges

    # Generic fallback: Haar graphs found by random search.
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
