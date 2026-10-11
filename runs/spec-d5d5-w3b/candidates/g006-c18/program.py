import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: instead of algebraic bi-Cayley / multi-base lifts, run an
# annealing search directly on d-regular bipartite graphs. Each state is a
# bipartite graph on h + h vertices with every degree exactly d, starting from
# a random Haar (cyclic) graph. Moves are 2-switches (edge swaps) that keep
# degrees and bipartiteness. The cost is the number of ordered vertex pairs at
# distance more than D. The side size h grows whenever a zero-cost graph is found.
# ----------------------------------------------------------------------------


def _cost(n, adj, D):
    """Number of ordered vertex pairs at distance > D (zero means diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal(h, d, D, rng, end):
    """Anneal a d-regular bipartite graph with sides of size h to diameter <= D.

    Returns an edge list on 2h vertices (A = 0..h-1, B = h..2h-1), or None if
    the deadline `end` passes before cost reaches zero.
    """
    n = 2 * h
    shifts = rng.sample(range(h), d)
    adj = [[] for _ in range(n)]
    for a in range(h):
        for s in shifts:
            b = h + (a + s) % h
            adj[a].append(b)
            adj[b].append(a)

    cur = _cost(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, end - t0)

    while cur > 0:
        now = time.monotonic()
        if now >= end:
            return None
        frac = (now - t0) / span
        temp = 0.05 + 2.5 * (1.0 - frac)

        a1 = rng.randrange(h)
        a2 = rng.randrange(h)
        if a1 == a2:
            continue
        i = rng.randrange(d)
        j = rng.randrange(d)
        x1 = adj[a1][i]
        x2 = adj[a2][j]
        if x2 in adj[a1] or x1 in adj[a2]:
            continue

        saved = (adj[a1][:], adj[a2][:], adj[x1][:], adj[x2][:])
        adj[a1][i] = x2
        adj[a2][j] = x1
        adj[x1][adj[x1].index(a1)] = a2
        adj[x2][adj[x2].index(a2)] = a1

        new = _cost(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = new
        else:
            adj[a1][:] = saved[0]
            adj[a2][:] = saved[1]
            adj[x1][:] = saved[2]
            adj[x2][:] = saved[3]

    return [(a, x) for a in range(h) for x in adj[a]]


# ----------------------------------------------------------------------------
# Structured baselines (kept for D = 3, where they are optimal or near-optimal).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has 2d vertices and diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if d - 2 >= 3 and lib.is_prime_power(d - 2) and not lib.is_prime_power(d - 1):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                consider(n_a, e_a)
            except ValueError:
                pass
        if best[0] >= moore:
            return best

    # Annealing search: grow the side size h while zero-cost graphs are found.
    ok_h = best[0] // 2
    step = 8
    while time.monotonic() < deadline:
        h = ok_h + step
        if 2 * h > moore:
            if step > 1:
                step = max(1, step // 2)
                continue
            break

        now = time.monotonic()
        remaining = deadline - now
        end = min(deadline, now + max(1.0, 0.4 * remaining))
        res = _anneal(h, d, D, rng, end)

        if res is not None and consider(2 * h, res):
            ok_h = h
            step = min(16, step * 2)
        else:
            step = max(1, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], [tuple(e) for e in best[1]]
