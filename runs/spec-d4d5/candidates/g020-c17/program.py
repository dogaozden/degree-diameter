import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline constructions.
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (degree <= d, diameter 3)."""
    for q in range(d - 1, 1, -1):
        if q <= 32 and lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bold alternative: direct annealing over d-regular bipartite graphs.
#
# The graph has k vertices per side. Each side-A vertex a is joined to side-B
# vertex sig[i][a] for i = 0..d-1. The d permutations sig[i] are kept so that,
# for each a, the values sig[i][a] are pairwise distinct (no multi-edges).
# Each sig[i] is a permutation of range(k), so the graph is exactly d-regular.
# The cost is the number of ordered (source, target) pairs at distance > D,
# computed with bitset BFS.
# ----------------------------------------------------------------------------

def _cost(k, d, D, sig):
    """Number of (vertex, vertex) pairs at distance > D. Zero means diameter <= D."""
    N = 2 * k
    adj = [[] for _ in range(N)]
    for i in range(d):
        p = sig[i]
        for a in range(k):
            b = k + p[a]
            adj[a].append(b)
            adj[b].append(a)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        if new == reach:
            break
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _try_swap(sig, d, i, a, b):
    """Swap sig[i][a] and sig[i][b] if the no-multi-edge condition still holds. Return (x, y) or None."""
    p = sig[i]
    x, y = p[a], p[b]
    for j in range(d):
        if j != i:
            q = sig[j]
            if q[a] == y or q[b] == x:
                return None
    p[a], p[b] = y, x
    return x, y


def _anneal(k, d, D, rng, deadline, iters):
    """Simulated annealing over d-regular bipartite graphs with k vertices per side. Returns sig or None."""
    sig = [[(a + i) % k for a in range(k)] for i in range(d)]
    # Randomize the cyclic start with valid moves only.
    for _ in range(4 * k * d):
        i = rng.randrange(d)
        a, b = rng.sample(range(k), 2)
        _try_swap(sig, d, i, a, b)

    cost = _cost(k, d, D, sig)
    T0, Tend = 2.0, 0.15
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (Tend / T0) ** (t / iters)
        i = rng.randrange(d)
        a, b = rng.sample(range(k), 2)
        before = _try_swap(sig, d, i, a, b)
        if before is None:
            continue
        x, y = before
        c2 = _cost(k, d, D, sig)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            sig[i][a], sig[i][b] = x, y
    if cost == 0:
        return sig
    return None


def _edges_from_sig(k, d, sig):
    E = []
    for i in range(d):
        p = sig[i]
        for a in range(k):
            E.append((a, k + p[a]))
    return 2 * k, E


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])

    moore = lib._moore_bound(d, D)
    if best_n >= moore:
        return best

    # Bold search: anneal d-regular bipartite graphs, growing k one step at a time.
    k = best_n // 2 + 1
    while time.monotonic() < deadline and k <= moore // 2:
        sig = _anneal(k, d, D, rng, deadline, iters=15000)
        if sig is not None:
            n, e = _edges_from_sig(k, d, sig)
            consider(n, e)
            if best_n >= 2 * k:
                k += 1
        # On failure, retry the same k from a fresh random start.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
