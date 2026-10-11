import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graph: incidence graph of PG(2, q), q the largest prime power <= d - 2.
# Each vertex keeps spare degree d - (q + 1), which the search can use.
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Return (n, edges) of PG(2, q) incidence for the largest prime power q <= d - 2, or None."""
    for q in range(d - 2, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bipartite local search for diameter-D graphs (general, not structured).
# Starts from a valid bipartite graph, then repeatedly adds one vertex per side
# and repairs it by simulated annealing on the number of bad pairs.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D, via bitmask balls."""
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


def _wire(v, pool, adj, d, rng):
    """Join new vertex v to up to d - deg(v) random pool vertices with spare degree."""
    cands = [u for u in pool if u != v and len(adj[u]) < d and u not in adj[v]]
    rng.shuffle(cands)
    for u in cands[:max(0, d - len(adj[v]))]:
        adj[v].add(u)
        adj[u].add(v)


def _sa_grow(d, D, n0, e0, rng, deadline, cap=15000):
    """Grow a valid bipartite graph by one vertex per side, repairing with annealing.

    Left side is 0..m-1 and right side is m..n0-1 (matches the incidence graph layout).
    Returns the largest valid (n, edges) found; always valid.
    """
    adj = [set() for _ in range(n0)]
    for u, v in e0:
        adj[u].add(v)
        adj[v].add(u)
    m = n0 // 2
    Lv = list(range(m))
    Rv = list(range(m, n0))
    best = (n0, list(e0))
    T = 0.5

    while time.monotonic() < deadline:
        n = len(adj)
        cost = _bad(n, adj, D)
        it = 0
        while cost > 0 and it < cap and time.monotonic() < deadline:
            it += 1
            x = rng.choice(Lv)
            y = rng.choice(Rv)
            if y in adj[x]:
                continue
            removed = []
            # Free a slot at x and at y if they are full. Neither removed edge can be (x, y).
            if len(adj[x]) >= d:
                r = rng.choice(tuple(adj[x]))
                adj[x].discard(r)
                adj[r].discard(x)
                removed.append((x, r))
            if len(adj[y]) >= d:
                r = rng.choice(tuple(adj[y]))
                adj[y].discard(r)
                adj[r].discard(y)
                removed.append((y, r))
            adj[x].add(y)
            adj[y].add(x)
            c2 = _bad(n, adj, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                adj[x].discard(y)
                adj[y].discard(x)
                for a, b in removed:
                    adj[a].add(b)
                    adj[b].add(a)
        if cost > 0:
            break  # repair stalled; keep the last valid graph
        n = len(adj)
        best = (n, [(u, v) for u in range(n) for v in adj[u] if u < v])
        # Grow: one new left and one new right vertex, wired to spare degree.
        new_l = len(adj)
        adj.append(set())
        Lv.append(new_l)
        new_r = len(adj)
        adj.append(set())
        Rv.append(new_r)
        _wire(new_l, Rv, adj, d, rng)
        _wire(new_r, Lv, adj, d, rng)
    return best


# ----------------------------------------------------------------------------
# Main entry point.
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
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Moore-optimal D = 3 case.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    # Araujo-Pardo & Lopez record family for D = 3.
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except (ValueError, StopIteration, KeyError):
            pass

    # Bold change: unstructured annealed growth from a PG(2, q) base with spare degree.
    base = _pg_base(d)
    if base is not None:
        n0, e0 = base
        if n0 <= 2 * d * d + 2 * d:  # keep the search space manageable
            consider(n0, e0)
            n_s, e_s = _sa_grow(d, D, n0, e0, rng, deadline)
            consider(n_s, e_s)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
