import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Helpers on adjacency-set representation.
# ----------------------------------------------------------------------------

def _adj_from(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _edges_of(adj):
    return [(v, u) for v in range(len(adj)) for u in adj[v] if v < u]


def _colour(n, adj):
    """Proper 2-colouring of adj, or None if the graph is not bipartite."""
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
                elif col[v] == col[u]:
                    return None
    return col


def _bad(n, adj, R):
    """Number of unordered pairs at distance > R (bitmask reachability)."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        if nxt == reach:
            break
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _apply(adj, rem, add):
    for a, b in rem:
        adj[a].discard(b)
        adj[b].discard(a)
    for a, b in add:
        adj[a].add(b)
        adj[b].add(a)


# ----------------------------------------------------------------------------
# Degree-preserving proposals (all keep bipartiteness and max degree <= d).
# ----------------------------------------------------------------------------

def _oriented(v, u, col):
    return (v, u) if col[v] == 0 else (u, v)


def _propose(adj, col, d, rng):
    n = len(adj)
    r = rng.random()
    if r < 0.4:
        # 2-switch: (a1,c1),(a2,c2) -> (a1,c2),(a2,c1).
        v1, v2 = rng.randrange(n), rng.randrange(n)
        if not adj[v1] or not adj[v2]:
            return None
        u1 = rng.choice(tuple(adj[v1]))
        u2 = rng.choice(tuple(adj[v2]))
        a1, c1 = _oriented(v1, u1, col)
        a2, c2 = _oriented(v2, u2, col)
        if a1 == a2 or c1 == c2:
            return None
        if c2 in adj[a1] or c1 in adj[a2]:
            return None
        return [(a1, c1), (a2, c2)], [(a1, c2), (a2, c1)]
    if r < 0.8:
        # Slide: deficient x takes over edge (y,z) from y's neighbour z.
        deficient = [v for v in range(n) if len(adj[v]) < d]
        if not deficient:
            return None
        x = rng.choice(deficient)
        y = rng.randrange(n)
        if col[y] == col[x] or y in adj[x] or not adj[y]:
            return None
        z = rng.choice(tuple(adj[y]))
        return [(y, z)], [(x, y)]
    # Plain addition between two deficient opposite-side vertices.
    dA = [v for v in range(n) if col[v] == 0 and len(adj[v]) < d]
    dB = [v for v in range(n) if col[v] == 1 and len(adj[v]) < d]
    if not dA or not dB:
        return None
    x = rng.choice(dA)
    y = rng.choice(dB)
    if y in adj[x]:
        return None
    return [], [(x, y)]


# ----------------------------------------------------------------------------
# Simulated annealing that tries to reach zero bad pairs.
# ----------------------------------------------------------------------------

def _anneal(n, adj, col, d, R, rng, deadline):
    cost = _bad(n, adj, R)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return False
        frac = (now - start) / span
        T = 0.6 * (1.0 - frac) + 0.05
        prop = _propose(adj, col, d, rng)
        if prop is None:
            continue
        rem, add = prop
        _apply(adj, rem, add)
        c2 = _bad(n, adj, R)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _apply(adj, add, rem)
    return True


def _grow(n, edges, d, R, deadline, rng):
    """Repeatedly add a vertex pair (one per side) and repair with annealing."""
    adj0 = _adj_from(n, edges)
    col0 = _colour(n, adj0)
    if col0 is None:
        return n, edges
    best_n, best_adj, best_col = n, adj0, col0
    fails = 0
    while time.monotonic() < deadline and fails < 3:
        now = time.monotonic()
        remaining = deadline - now
        adj = [set(s) for s in best_adj]
        col = list(best_col)
        adj.append(set())
        col.append(0)
        adj.append(set())
        col.append(1)
        n2 = best_n + 2
        ok = _anneal(n2, adj, col, d, R, rng, now + max(1.0, remaining * 0.5))
        if ok:
            best_n, best_adj, best_col = n2, adj, col
            fails = 0
        else:
            fails += 1
    return best_n, _edges_of(best_adj)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(0.1, min(0.85 * time_limit, time_limit - 3.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Algebraic constructions.
    if D >= 3:
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            try:
                consider(*lib.projective_plane_incidence(d - 1))
            except (ValueError, StopIteration, KeyError):
                pass
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except (ValueError, StopIteration, KeyError):
                pass

    # Already at the Moore bound: nothing to search.
    if best_n >= lib._moore_bound(d, D):
        return best

    # Growth search from the best valid base.
    try:
        n2, e2 = _grow(best_n, best[1], d, D, deadline, rng)
        consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
