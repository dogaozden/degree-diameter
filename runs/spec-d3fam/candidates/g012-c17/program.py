import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions (safe, known-valid starting points).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _ara(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Helpers.
# ----------------------------------------------------------------------------

def _graph_adj(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given as neighbour sets; None if not bipartite."""
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


def _cost(N, adj, D):
    """Number of unordered pairs at distance > D (disconnected pairs included). Zero means diameter <= D."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# Different family: simulated annealing over the edge set, with vertex insertion.
#
# State: a bipartite graph (fixed two-colouring) with max degree <= d.
# Objective: number of pairs at distance > D. Moves rewire one edge endpoint
# or add an edge between two spare-degree opposite vertices. Once the cost hits
# zero, the graph is reported and one more vertex is inserted (its d neighbours
# are taken from the opposite side, stealing one edge from each saturated
# neighbour), and the search continues.
# ----------------------------------------------------------------------------

def _sa_grow(n, edges, color, d, D, deadline, rng, report):
    color = list(color)
    adj = _graph_adj(n, edges)
    E = []
    for u, v in edges:
        E.append([u, v] if color[u] == 0 else [v, u])
    A = [v for v in range(n) if color[v] == 0]
    B = [v for v in range(n) if color[v] == 1]

    def add_vertex(s):
        v = len(color)
        color.append(s)
        adj.append(set())
        opp = B if s == 0 else A
        cand = list(opp)
        rng.shuffle(cand)
        free = [x for x in cand if len(adj[x]) < d]
        full = [x for x in cand if len(adj[x]) >= d]
        chosen = (free + full)[:d]
        pos = 1 - s  # index in E holding the opposite-side endpoint
        for x in chosen:
            if len(adj[x]) >= d:
                idxs = [i for i, e in enumerate(E) if e[pos] == x]
                i = rng.choice(idxs)
                p, q = E[i]
                adj[p].discard(q)
                adj[q].discard(p)
                E[i] = E[-1]
                E.pop()
            adj[v].add(x)
            adj[x].add(v)
            E.append([v, x] if s == 0 else [x, v])
        (A if s == 0 else B).append(v)

    cost = _cost(len(color), adj, D)
    since = 0
    while time.monotonic() < deadline:
        if cost == 0:
            N = len(color)
            el = [(a, b) for a, b in E]
            report(N, el)
            add_vertex(rng.randrange(2))
            cost = _cost(len(color), adj, D)
            since = 0
            continue

        since += 1
        T = 0.08 + 0.6 * math.exp(-since / 1500.0)

        if E and rng.random() < 0.85:
            i = rng.randrange(len(E))
            a, b = E[i]
            if rng.random() < 0.5:
                # Keep a, move the B-endpoint.
                nb = None
                for _ in range(20):
                    c = B[rng.randrange(len(B))]
                    if c != b and len(adj[c]) < d and c not in adj[a]:
                        nb = c
                        break
                if nb is None:
                    continue
                na = a
            else:
                # Keep b, move the A-endpoint.
                na = None
                for _ in range(20):
                    c = A[rng.randrange(len(A))]
                    if c != a and len(adj[c]) < d and c not in adj[b]:
                        na = c
                        break
                if na is None:
                    continue
                nb = b
            adj[a].discard(b)
            adj[b].discard(a)
            adj[na].add(nb)
            adj[nb].add(na)
            E[i] = [na, nb]
            c2 = _cost(len(color), adj, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                adj[na].discard(nb)
                adj[nb].discard(na)
                adj[a].add(b)
                adj[b].add(a)
                E[i] = [a, b]
        else:
            # Add an edge between two spare-degree opposite vertices.
            found = None
            for _ in range(20):
                a2 = A[rng.randrange(len(A))]
                b2 = B[rng.randrange(len(B))]
                if len(adj[a2]) < d and len(adj[b2]) < d and b2 not in adj[a2]:
                    found = (a2, b2)
                    break
            if found is None:
                continue
            a2, b2 = found
            adj[a2].add(b2)
            adj[b2].add(a2)
            E.append([a2, b2])
            c2 = _cost(len(color), adj, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                E.pop()
                adj[a2].discard(b2)
                adj[b2].discard(a2)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        ara = _ara(d)
        if ara is not None:
            consider(ara[0], ara[1])
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Annealed growth from the best valid base graph.
    adj0 = _graph_adj(best_n, best_e)
    color0 = _bipartition(best_n, adj0)
    if color0 is not None:
        _sa_grow(best_n, best_e, color0, d, D, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
