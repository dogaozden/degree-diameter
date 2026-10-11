import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: direct annealing over simple bipartite d-regular graphs.
#
# Instead of searching group lifts, start from a circulant bipartite d-regular
# graph on sides of size s and anneal with degree-preserving double edge swaps.
# The cost is the number of vertex pairs at distance > D, counted with bitmask
# ball expansion. Sides grow one at a time; the best valid graph is kept.
# ----------------------------------------------------------------------------

def _bad(n, nb, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal(s, d, D, rng, deadline):
    """Anneal a bipartite d-regular graph with sides of size s to diameter <= D.

    Vertices: A-side 0..s-1, B-side s..2s-1. Returns an edge list or None on timeout.
    """
    n = 2 * s
    nb = [set() for _ in range(n)]
    E = []
    for a in range(s):
        for l in range(d):
            b = s + (a + l) % s
            E.append([a, b])
            nb[a].add(b)
            nb[b].add(a)
    cost = _bad(n, nb, D)
    if cost == 0:
        return [(a, b) for a, b in E]

    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    T0, T1 = 2.0, 0.05
    T = T0
    it = 0
    while True:
        it += 1
        if (it & 7) == 0:
            now = time.monotonic()
            if now > deadline:
                return None
            frac = min(1.0, (now - t0) / span)
            T = T0 * (T1 / T0) ** frac

        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in nb[a1] or b1 in nb[a2]:
            continue

        # Apply swap (a1-b1, a2-b2) -> (a1-b2, a2-b1).
        nb[a1].discard(b1)
        nb[b1].discard(a1)
        nb[a2].discard(b2)
        nb[b2].discard(a2)
        nb[a1].add(b2)
        nb[b2].add(a1)
        nb[a2].add(b1)
        nb[b1].add(a2)
        E[i] = [a1, b2]
        E[j] = [a2, b1]

        c2 = _bad(n, nb, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                return [(a, b) for a, b in E]
        else:
            # Revert.
            nb[a1].discard(b2)
            nb[b2].discard(a1)
            nb[a2].discard(b1)
            nb[b1].discard(a2)
            nb[a1].add(b1)
            nb[b1].add(a1)
            nb[a2].add(b2)
            nb[b2].add(a2)
            E[i] = [a1, b1]
            E[j] = [a2, b2]


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D}: 2-regular, bipartite, diameter D.
        n = 2 * D
        edges = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, edges, d, D):
            return n, edges
        return 4, [(0, 1), (1, 2), (2, 3), (3, 0)]

    # Safe fallback: K_{d,d}, diameter 2 <= D.
    best = lib.haar_graph(d, range(d))

    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    rng = random.Random(seed * 1000003 + d * 131 + D)
    s = best[0] // 2 + 1
    while time.monotonic() < deadline and s <= moore // 2:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(2.0, 0.3 * remaining))
        E = _anneal(s, d, D, rng, slice_end)
        if E is not None:
            consider(2 * s, E)
            s = max(s + 1, best[0] // 2 + 1)
        # On failure, retry the same s with fresh randomness until time runs out.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
