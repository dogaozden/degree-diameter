import math
import random
import time

import lib

# Largest total vertex count the annealer will handle (keeps each cost evaluation fast).
_MAX_N = 600


def _ball_cost(N, adj, D):
    """Number of unordered vertex pairs at distance > D, computed with bitmask balls."""
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


def _replace(lst, old, new):
    lst[lst.index(old)] = new


def _switch(adj, a1, i, a2, j, b1, b2):
    """Set edges a1-b2 (at slot i of a1) and a2-b1 (at slot j of a2), replacing a1-b1 and a2-b2.

    Calling it again with (b2, b1) in place of (b1, b2) undoes the move.
    """
    adj[a1][i] = b2
    adj[a2][j] = b1
    _replace(adj[b1], a1, a2)
    _replace(adj[b2], a2, a1)


def _anneal(d, D, m, rng, deadline):
    """Search a d-regular bipartite graph on sides of size m with diameter <= D.

    Starts from a random circulant (Haar) graph and applies degree-preserving
    edge switches under simulated annealing on the number of far pairs.
    Vertices: A-side 0..m-1, B-side m..2m-1. Returns the edge list or None.
    """
    N = 2 * m
    shifts = rng.sample(range(m), d)
    adj = [[] for _ in range(N)]
    for a in range(m):
        for s in shifts:
            b = m + (a + s) % m
            adj[a].append(b)
            adj[b].append(a)

    cost = _ball_cost(N, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 2.0 * (0.03 ** ((now - t0) / span))

        a1 = rng.randrange(m)
        a2 = rng.randrange(m)
        if a1 == a2:
            continue
        i = rng.randrange(d)
        j = rng.randrange(d)
        b1 = adj[a1][i]
        b2 = adj[a2][j]
        if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue

        _switch(adj, a1, i, a2, j, b1, b2)
        c2 = _ball_cost(N, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _switch(adj, a1, i, a2, j, b2, b1)

    if cost != 0:
        return None
    return [(a, b) for a in range(m) for b in adj[a]]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Calibration: projective plane incidence graph of PG(2, q), q the largest prime power <= d-1.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
        if best_n > 2 * d:
            return best

    rng = random.Random(seed)

    # Main search: annealed bipartite graphs with a circulant start, climbing m upward.
    moore_side = lib._moore_bound(d, D) // 2
    m = max(d + 1, moore_side // 3)
    while time.monotonic() < deadline:
        if 2 * m > _MAX_N:
            break
        remaining = deadline - time.monotonic()
        slice_end = time.monotonic() + max(1.0, remaining * 0.35)
        res = _anneal(d, D, m, rng, min(deadline, slice_end))
        if res is not None:
            consider(2 * m, res)
            m += 1
        # On failure, keep the same m and retry with fresh randomness.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
