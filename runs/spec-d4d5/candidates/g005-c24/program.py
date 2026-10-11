import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured candidates (cheap, always tried first).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 25), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Unstructured search: bipartite d-regular graphs on k + k vertices, annealed
# over degree-preserving double-edge swaps. Cost = number of vertex pairs at
# distance > D. Zero cost means diameter <= D.
# ----------------------------------------------------------------------------

def _pair_cost(N, adj, D):
    """Number of unordered vertex pairs at distance > D (bitmask BFS)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _anneal_regular(d, D, k, rng, deadline):
    """Try to find a bipartite d-regular graph on k+k vertices with diameter <= D.

    Starts from a circulant (A_a ~ B_{a+s}, s < d) and performs random swaps:
    edges (a1,b1),(a2,b2) become (a1,b2),(a2,b1) when that creates no parallel edge.
    Returns (n, edges) on success, else None.
    """
    if k < d or d < 2:
        return None
    N = 2 * k
    adj = [[] for _ in range(N)]
    E = []
    for a in range(k):
        for s in range(d):
            b = (a + s) % k
            E.append([a, b])
            adj[a].append(k + b)
            adj[k + b].append(a)

    def swap(i, j):
        """Apply the swap of edges i and j; return the old (a1,b1,a2,b2) or None if illegal."""
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            return None
        if (k + b2) in adj[a1] or (k + b1) in adj[a2]:
            return None
        adj[a1].remove(k + b1); adj[k + b1].remove(a1)
        adj[a2].remove(k + b2); adj[k + b2].remove(a2)
        adj[a1].append(k + b2); adj[k + b2].append(a1)
        adj[a2].append(k + b1); adj[k + b1].append(a2)
        E[i] = [a1, b2]
        E[j] = [a2, b1]
        return (a1, b1, a2, b2)

    def unswap(i, j, old):
        a1, b1, a2, b2 = old
        adj[a1].remove(k + b2); adj[k + b2].remove(a1)
        adj[a2].remove(k + b1); adj[k + b1].remove(a2)
        adj[a1].append(k + b1); adj[k + b1].append(a1)
        adj[a2].append(k + b2); adj[k + b2].append(a2)
        E[i] = [a1, b1]
        E[j] = [a2, b2]

    def out_edges():
        return (N, [(a, v) for a in range(k) for v in adj[a]])

    # Mix the circulant without cost checks so the start is not structured.
    m = len(E)
    for _ in range(4 * m):
        i, j = rng.randrange(m), rng.randrange(m)
        if i != j:
            swap(i, j)

    cost = _pair_cost(N, adj, D)
    if cost == 0:
        return out_edges()

    T = 0.6
    while time.monotonic() < deadline:
        i, j = rng.randrange(m), rng.randrange(m)
        if i == j:
            continue
        old = swap(i, j)
        if old is None:
            continue
        nc = _pair_cost(N, adj, D)
        delta = nc - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = nc
            if cost == 0:
                return out_edges()
        else:
            unswap(i, j, old)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
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
        # Araujo-Pardo & López record family: degree q+2 with q = d-2 a prime power >= 3.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except (ValueError, AssertionError):
                pass

    if D >= 3 and d >= 2:
        # Unstructured annealing over bipartite d-regular graphs, adaptive in k.
        k = max(d + 1, best_n // 2 + 1)
        while time.monotonic() < deadline - 0.5:
            remaining = deadline - time.monotonic()
            budget = min(remaining, max(2.0, 0.35 * remaining))
            res = _anneal_regular(d, D, k, rng, time.monotonic() + budget)
            if res is not None:
                consider(res[0], res[1])
                k = max(k + 1, k + k // 25)
            else:
                if k > best_n // 2 + 1:
                    k -= 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
