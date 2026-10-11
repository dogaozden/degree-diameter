import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions (D = 3 focus).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW: deficit annealing growth.
#
# Given a valid bipartite graph G (max degree <= d, diameter <= D), add two
# new vertices, one on each side. Their degrees start at 0 ("deficit" d each).
# Instead of requiring the old graph to stay fixed, a simulated annealing walk
# moves over graphs with max degree <= d, using three move types:
#   close    : join two deficient vertices on opposite sides;
#   transfer : give a deficient vertex x the edge (a, b) of a random vertex b,
#              i.e. replace (a, b) by (x, b), which moves the deficit to a;
#   switch   : degree-preserving 2-switch on two edges of the same side pattern.
# Cost = (number of vertex pairs at distance > D) + W * (total deficit).
# Any zero-cost state is a valid graph with 2 more vertices than G.
# Unlike a fixed-edge repair, the deficit can wander through the whole graph,
# so the graph can reorganise globally while every move stays degree-legal.
# ----------------------------------------------------------------------------

def _colour(n, adj):
    """Two-colouring of the first n vertices (their neighbours are < n)."""
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
    return color


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitmask ball method)."""
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


def _apply(adj, ops):
    for k, u, v in ops:
        if k == 'a':
            adj[u].add(v)
            adj[v].add(u)
        else:
            adj[u].discard(v)
            adj[v].discard(u)


def _inverse(ops):
    return [('r' if k == 'a' else 'a', u, v) for k, u, v in reversed(ops)]


def _propose(n, adj, side, d, defs, rng):
    """Random legal move as a list of (kind, u, v) operations, or None."""
    r = rng.random()
    if defs and r < 0.4:
        x = rng.choice(defs)
        ys = [y for y in defs if side[y] != side[x] and y not in adj[x]]
        if ys:
            return [('a', x, rng.choice(ys))]
    if defs and r < 0.8:
        x = rng.choice(defs)
        bs = [b for b in range(n) if side[b] != side[x] and b not in adj[x] and adj[b]]
        if not bs:
            return None
        b = rng.choice(bs)
        a = rng.choice(list(adj[b]))
        return [('r', a, b), ('a', x, b)]
    # 2-switch on two edges whose endpoints lie on the same sides.
    a1 = rng.randrange(n)
    if not adj[a1]:
        return None
    b1 = rng.choice(list(adj[a1]))
    cands = [v for v in range(n) if side[v] == side[a1] and v != a1 and adj[v]]
    if not cands:
        return None
    a2 = rng.choice(cands)
    b2 = rng.choice(list(adj[a2]))
    if b2 in adj[a1] or b1 in adj[a2] or b1 == b2:
        return None
    return [('r', a1, b1), ('r', a2, b2), ('a', a1, b2), ('a', a2, b1)]


def _grow_one(n0, edges, d, D, deadline, rng, W=3):
    """Try to extend a valid graph on n0 vertices to n0 + 2 vertices; return (n, edges) or None."""
    n = n0 + 2
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    side = _colour(n0, adj) + [0, 1]

    def deficit():
        return sum(d - len(a) for a in adj)

    def total():
        return _bad(n, adj, D) + W * deficit()

    cost = total()
    T0, T1 = 1.5, 0.08
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t_start) / span
        T = T0 * (T1 / T0) ** frac
        defs = [v for v in range(n) if len(adj[v]) < d]
        ops = _propose(n, adj, side, d, defs, rng)
        if not ops:
            continue
        _apply(adj, ops)
        c2 = total()
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _apply(adj, _inverse(ops))
    out = sorted({(min(u, v), max(u, v)) for u in range(n) for v in adj[u]})
    return n, out


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 0.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        # Moore-optimal case: PG(2, d-1) incidence graph.
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best
        # Araujo-Pardo & Lopez record family for d-2 a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except (ValueError, StopIteration, KeyError):
                pass
        if best[0] <= 2 * (d + 1):
            pg = _best_pg(d)
            if pg is not None:
                consider(*pg)

    # Grow the best base by two vertices at a time with deficit annealing.
    moore = lib._moore_bound(d, D)
    cur_n, cur_e = best
    while time.monotonic() < deadline and cur_n + 2 <= moore:
        res = _grow_one(cur_n, cur_e, d, D, deadline, rng)
        if res is None:
            break
        n2, e2 = res
        if not lib.is_valid(n2, e2, d, D):
            break
        cur_n, cur_e = n2, e2
        best = (n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
