import math
import random
import time

import lib


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance greater than D (bitmask BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt[v] = r
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _set_pairs(E, S, adj, i, j, p, q):
    """Replace edges E[i], E[j] with p, q, keeping the edge set S and adjacency lists in sync."""
    a, b = E[i]
    c, e = E[j]
    S.discard((a, b))
    S.discard((c, e))
    adj[a].remove(b)
    adj[b].remove(a)
    adj[c].remove(e)
    adj[e].remove(c)
    E[i] = p
    E[j] = q
    for x, y in (p, q):
        S.add((x, y))
        adj[x].append(y)
        adj[y].append(x)


def _anneal(m, d, D, rng, deadline):
    """Search a simple d-regular bipartite graph on 2m vertices with diameter <= D.

    Left vertices are 0..m-1, right vertices are m..2m-1. Moves are double edge
    switches, which preserve regularity and bipartiteness. Returns the edge list
    (pairs (left, right)) on success, else None.
    """
    n = 2 * m
    E = []
    S = set()
    adj = [[] for _ in range(n)]
    for a in range(m):
        for s in range(d):
            b = m + (a + s) % m
            E.append((a, b))
            S.add((a, b))
            adj[a].append(b)
            adj[b].append(a)
    L = len(E)
    for _ in range(4 * L):
        i = rng.randrange(L)
        j = rng.randrange(L)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in S or (a2, b1) in S:
            continue
        _set_pairs(E, S, adj, i, j, (a1, b2), (a2, b1))

    cost = _bad_pairs(n, adj, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T0, T1 = 2.0, 0.15
    T = T0
    it = 0
    while cost > 0:
        it += 1
        if (it & 15) == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            frac = (now - start) / span
            T = T0 * (T1 / T0) ** frac
        i = rng.randrange(L)
        j = rng.randrange(L)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in S or (a2, b1) in S:
            continue
        old_p, old_q = (a1, b1), (a2, b2)
        _set_pairs(E, S, adj, i, j, (a1, b2), (a2, b1))
        c2 = _bad_pairs(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _set_pairs(E, S, adj, i, j, old_p, old_q)
    return list(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if d == 2 and D >= 2:
        # Even cycle C_{2D} is bipartite with diameter D.
        cyc = 2 * D
        consider(cyc, [(i, (i + 1) % cyc) for i in range(cyc)])

    if D >= 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])

    bound = _moore(d, D)
    if d >= 3 and D >= 3 and best_n < bound:
        rng = random.Random(seed * 1000003 + d * 31 + D)
        m = max(d, best_n // 2 + 1)
        while time.monotonic() < deadline and 2 * m <= bound:
            remaining = deadline - time.monotonic()
            dur = min(remaining, max(2.0, 0.2 * remaining))
            res = _anneal(m, d, D, rng, time.monotonic() + dur)
            if res is not None:
                consider(2 * m, [(a, b) for a, b in res])
                m += 1
            # On failure, retry the same m with a fresh random start.

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
