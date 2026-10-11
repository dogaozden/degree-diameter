import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bad_pairs_adj(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (bitset BFS)."""
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


def _replace(E, S, adj, L, i, na, nb):
    """Replace bipartite edge i (local indices a in [0,L), b in [0,L)) by (na, nb), keeping adj and key set S in sync."""
    a, b = E[i]
    S.discard(a * L + b)
    adj[a].remove(L + b)
    adj[L + b].remove(a)
    S.add(na * L + nb)
    adj[na].append(L + nb)
    adj[L + nb].append(na)
    E[i] = (na, nb)


def _anneal_regular(L, d, D, deadline, rng):
    """Search a simple d-regular bipartite graph on L + L vertices with diameter <= D.

    Starts from a circulant and applies double-edge swaps (which preserve
    regularity and bipartiteness), annealing on the number of bad pairs.
    Returns the edge list as local index pairs (a, b), or None.
    """
    if L < d or d < 1:
        return None
    n = 2 * L
    E = [(a, (a + s) % L) for a in range(L) for s in range(d)]
    m = len(E)
    S = {a * L + b for a, b in E}
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(L + b)
        adj[L + b].append(a)

    # Randomise the start with degree-preserving swaps.
    for _ in range(4 * m):
        i, j = rng.randrange(m), rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if a1 * L + b2 in S or a2 * L + b1 in S:
            continue
        _replace(E, S, adj, L, i, a1, b2)
        _replace(E, S, adj, L, j, a2, b1)

    cost = _bad_pairs_adj(n, adj, D)
    t0 = time.monotonic()
    budget = max(1e-6, deadline - t0)
    T0, T_end = 2.0, 0.2
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - t0) / budget)
        T = T0 * (T_end / T0) ** frac

        i, j = rng.randrange(m), rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if a1 * L + b2 in S or a2 * L + b1 in S:
            continue
        _replace(E, S, adj, L, i, a1, b2)
        _replace(E, S, adj, L, j, a2, b1)
        c2 = _bad_pairs_adj(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _replace(E, S, adj, L, j, a2, b2)
            _replace(E, S, adj, L, i, a1, b1)

    if cost == 0:
        return list(E)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fast path: projective plane meets the Moore bound when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    deadline = start + 0.8 * time_limit

    # New family for D >= 3: direct annealing over simple d-regular bipartite
    # graphs with growing side size L, instead of lifts or polygon extensions.
    if D >= 3 and d >= 3:
        moore = lib.moore_bound(d, D)
        L = max(d, best_n // 2 + 1)
        while time.monotonic() < deadline:
            if 2 * L > moore:
                break
            now = time.monotonic()
            remaining = deadline - now
            budget = min(remaining, max(3.0, remaining / 3.0))
            res = _anneal_regular(L, d, D, now + budget, rng)
            if res is None:
                break
            n = 2 * L
            edges = [(a, L + b) for a, b in res]
            consider(n, edges)
            L += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
