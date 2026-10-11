import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Moore bound and structure helpers.
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Largest possible order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _random_regular(h, d, rng):
    """Random d-regular bipartite graph with parts 0..h-1 and h..2h-1, built from d disjoint perfect matchings."""
    adj = [[] for _ in range(2 * h)]
    for _ in range(d):
        perm = None
        for _attempt in range(300):
            cand = list(range(h))
            rng.shuffle(cand)
            if all(cand[x] + h not in adj[x] for x in range(h)):
                perm = cand
                break
        if perm is None:
            return None
        for x in range(h):
            y = perm[x] + h
            adj[x].append(y)
            adj[y].append(x)
    return adj


def _cost(N, adj, D):
    """Number of unordered vertex pairs at distance more than D. Zero means diameter <= D."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _edges_of(h, adj):
    """Edge list from the A-side adjacency (A vertices are 0..h-1)."""
    return [(x, y) for x in range(h) for y in adj[x]]


def _anneal(N, d, D, h, adj, rng, deadline):
    """Edge-switch simulated annealing on a d-regular bipartite graph; cost = bad pairs.

    A move picks two A-side edges (x1,y1), (x2,y2) and replaces them with (x1,y2), (x2,y1),
    which keeps every degree equal to d and keeps the graph simple. The temperature
    cools geometrically with elapsed time, so the schedule adapts to the time budget.
    Returns the adjacency structure when cost reaches zero, otherwise None.
    """
    cur = _cost(N, adj, D)
    if cur == 0:
        return adj
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0 = max(1.0, 0.03 * cur)
    T1 = 0.15
    T = T0
    it = 0
    while True:
        it += 1
        if (it & 31) == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        x1 = rng.randrange(h)
        x2 = rng.randrange(h)
        if x1 == x2:
            continue
        i = rng.randrange(d)
        j = rng.randrange(d)
        y1 = adj[x1][i]
        y2 = adj[x2][j]
        if y1 == y2 or y2 in adj[x1] or y1 in adj[x2]:
            continue
        # Apply the switch.
        adj[x1][i] = y2
        adj[x2][j] = y1
        adj[y1][adj[y1].index(x1)] = x2
        adj[y2][adj[y2].index(x2)] = x1
        c2 = _cost(N, adj, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
            if cur == 0:
                return adj
        else:
            # Revert the switch.
            adj[x1][i] = y1
            adj[x2][j] = y2
            adj[y1][adj[y1].index(x2)] = x1
            adj[y2][adj[y2].index(x1)] = x2


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.75 * time_limit, time_limit - 8.0))
    deadline = start + budget

    if d < 1:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    # Projective-plane incidence graph (diameter 3) as a stronger fallback.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best_n and lib.is_valid(pg[0], pg[1], d, D):
            best_n, best_e = pg

    # Main search: anneal d-regular bipartite graphs of increasing order.
    # Each success is verified, kept, and the order is raised by 2.
    if D >= 3 and d >= 2:
        rng = random.Random(seed * 1000003 + d * 131 + D)
        bound = _moore(d, D)
        N = best_n + 2
        while time.monotonic() < deadline - 0.5 and N <= bound:
            h = N // 2
            if h < d:
                N += 2
                continue
            adj = None
            for _ in range(40):
                adj = _random_regular(h, d, rng)
                if adj is not None:
                    break
            if adj is None:
                break
            now = time.monotonic()
            remaining = deadline - now
            res = _anneal(N, d, D, h, adj, rng, now + 0.5 * remaining)
            if res is None:
                continue
            e = _edges_of(h, res)
            if lib.is_valid(N, e, d, D):
                best_n, best_e = N, e
                N += 2
            else:
                continue

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
