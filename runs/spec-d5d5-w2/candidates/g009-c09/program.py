"""Bitset-accelerated cyclic Haar-graph search for bipartite graphs of max degree d and diameter D.

A Haar graph over Z_N with connection set S joins A_x to B_{x+s} for s in S. Translation
x -> x + t is an automorphism, so checking eccentricities from A_0 and B_0 suffices. Each
BFS layer is a union of cyclic bit-rotations of Python integers, which makes candidate
evaluation much cheaper than a list-based BFS. Hill climbing over S with stall restarts
searches for zero unreached pairs. A valid K_{d,d} (or projective plane for D = 3) is the
fallback, and every result is checked with lib.is_valid before it is returned.
"""
import random
import time

import lib


def _unreached(N, S, neg, D, mask):
    """Count (source, target) pairs at distance > D, from A_0 and from B_0."""
    total = 2 * N * 2
    for start in (0, 1):
        vis = [0, 0]
        vis[start] = 1
        f = 1
        side = start
        for _ in range(D):
            shifts = S if side == 0 else neg
            nf = 0
            for t in shifts:
                nf |= ((f << t) | (f >> (N - t))) & mask
            other = 1 - side
            nf &= ~vis[other]
            if not nf:
                break
            vis[other] |= nf
            f = nf
            side = other
        total -= vis[0].bit_count() + vis[1].bit_count()
    return total


def _search(N, d, D, rng, deadline, climb_iters=4000, stall_limit=400):
    """Return a connection set S (size d, containing 0) with zero unreached pairs, or None."""
    if N < d:
        return None
    mask = (1 << N) - 1
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, N), d - 1)
        neg = [(N - s) % N for s in S]
        cur = _unreached(N, S, neg, D, mask)
        stall = 0
        for it in range(climb_iters):
            if cur == 0:
                break
            if (it & 127) == 0 and time.monotonic() > deadline:
                return None
            i = rng.randrange(1, d)
            c = rng.randrange(1, N)
            if c in S:
                continue
            S2 = S[:]
            S2[i] = c
            neg2 = [(N - s) % N for s in S2]
            v = _unreached(N, S2, neg2, D, mask)
            if v < cur:
                stall = 0
            else:
                stall += 1
            if v <= cur:
                S, cur, neg = S2, v, neg2
            if stall > stall_limit:
                break
        if cur == 0:
            return S
    return None


def _haar_edges(N, S):
    """Edges of the Haar graph: A_x = x, B_y = N + y, A_x ~ B_{x+s}."""
    return [(x, N + (x + s) % N) for x in range(N) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and order 2d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    # Structured baseline for D = 3: projective plane incidence graph.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                break

    # Main search: cyclic Haar lifts, aiming just above the current order.
    window = 3
    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if 2 * lo > moore:
            break
        N = lo + rng.randrange(window)
        if 2 * N > moore:
            N = lo
        slice_end = min(deadline, time.monotonic() + 4.0)
        S = _search(N, d, D, rng, slice_end)
        if S is not None:
            n2, e2 = 2 * N, _haar_edges(N, S)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
