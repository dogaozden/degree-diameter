import math
import random
import time

import lib


def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bad(adj, N, D):
    """Number of unordered vertex pairs at distance > D (bitset ball expansion)."""
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


def _swap(sigma, adj, m, t, i, j):
    """Exchange the R-partners of L-vertices i and j in matching t. Calling it twice undoes it."""
    a = sigma[t][i]
    b = sigma[t][j]
    adj[i].discard(m + a)
    adj[m + a].discard(i)
    adj[j].discard(m + b)
    adj[m + b].discard(j)
    adj[i].add(m + b)
    adj[m + b].add(i)
    adj[j].add(m + a)
    adj[m + a].add(j)
    sigma[t][i] = b
    sigma[t][j] = a


def _anneal_regular(d, D, m, rng, budget_end):
    """Search a d-regular bipartite graph on sides of size m with diameter <= D by edge-switch annealing.

    Each of the d perfect matchings is a permutation sigma_t; a move swaps two images inside one
    matching, which keeps the graph d-regular. Returns (n, edges) on success, else None.
    """
    N = 2 * m
    sigma = [[(i + t) % m for i in range(m)] for t in range(d)]  # distinct shifts: simple graph
    adj = [set() for _ in range(N)]
    for t in range(d):
        for i in range(m):
            b = sigma[t][i]
            adj[i].add(m + b)
            adj[m + b].add(i)
    cur = _bad(adj, N, D)
    T = 1.0
    it = 0
    while cur > 0:
        it += 1
        if (it & 7) == 0 and time.monotonic() > budget_end:
            return None
        T = max(0.2, T * 0.9995)
        t = rng.randrange(d)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a = sigma[t][i]
        b = sigma[t][j]
        if (m + b) in adj[i] or (m + a) in adj[j]:
            continue  # would create a parallel edge
        _swap(sigma, adj, m, t, i, j)
        new = _bad(adj, N, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            _swap(sigma, adj, m, t, i, j)
    edges = [(i, g) for i in range(m) for g in adj[i]]
    return N, edges


def _regular_search(d, D, m0, rng, deadline, consider):
    """Grow m while annealing succeeds; stop at the first failure."""
    m = max(d, m0)
    while time.monotonic() < deadline:
        now = time.monotonic()
        budget_end = now + max(1.0, 0.6 * (deadline - now))
        res = _anneal_regular(d, D, m, rng, min(budget_end, deadline))
        if res is None:
            break
        consider(res[0], res[1])
        m += 2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    rng = random.Random(seed * 1000003 + d * 97 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 2:
        # Even cycle C_{2D} is bipartite with diameter D and max degree 2.
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    if D >= 3:
        pg = _pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 3 and d >= 3:
        m0 = max(d, best[0] // 2)
        _regular_search(d, D, m0, rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
