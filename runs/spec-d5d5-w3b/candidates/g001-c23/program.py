import math
import random
import time

import lib


def _cost(m, E, D):
    """Number of unordered vertex pairs at distance > D in the bipartite graph.

    Vertices: A-side a -> a, B-side b -> m + b. E is a list of (a, b) pairs.
    """
    n = 2 * m
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(m + b)
        adj[m + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        changed = False
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
            if r != reach[v]:
                changed = True
        reach = new
        if not changed:
            break
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal(m, d, D, rng, deadline, T0=2.0):
    """Simulated annealing over d-regular bipartite graphs with m+m vertices.

    Moves are degree-preserving 2-switches. Returns the edge list (a, b) with
    zero bad pairs, or None if the deadline passes first.
    """
    S = rng.sample(range(m), d)
    E = [(i, (i + s) % m) for i in range(m) for s in S]  # simple, d-regular start
    eset = set(E)
    cost = _cost(m, E, D)
    if cost == 0:
        return E
    L = len(E)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = T0
    it = 0
    while True:
        now = time.monotonic()
        if now >= deadline:
            return None
        if it % 64 == 0:
            frac = (now - t0) / span
            T = max(0.05, T0 * (1.0 - frac))
        it += 1
        i = rng.randrange(L)
        j = rng.randrange(L)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        e1 = (a1, b2)
        e2 = (a2, b1)
        if e1 in eset or e2 in eset:
            continue
        E[i] = e1
        E[j] = e2
        eset.discard((a1, b1))
        eset.discard((a2, b2))
        eset.add(e1)
        eset.add(e2)
        new = _cost(m, E, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
            if cost == 0:
                return E
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            eset.discard(e1)
            eset.discard(e2)
            eset.add((a1, b1))
            eset.add((a2, b2))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + max(0.5, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    # Exact optimal construction for D = 3 when d-1 is a prime power.
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        n, edges = lib.projective_plane_incidence(q)
        if lib.is_valid(n, edges, d, D):
            return n, edges

    # Safe fallback: K_{d,d}.
    best_m = d
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        return best

    # Cheap cyclic Haar search (parent approach) for a better fallback.
    hdl = start + 0.2 * (end - start)
    m, misses = d + 1, 0
    while time.monotonic() < hdl and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= hdl:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                best_m = m
                break
        if found:
            best = found
            misses = 0
        else:
            misses += 1
        m += 1

    # Bold phase: annealed random regular bipartite graphs with growing side size,
    # searched by bracketing (exponential growth, then bisection).
    lo = best_m
    hi = None
    step = max(2, lo // 8)
    while True:
        now = time.monotonic()
        if now >= end - 0.2:
            break
        if hi is None:
            m = lo + step
        else:
            m = (lo + hi) // 2
            if m <= lo:
                break
        remaining = end - now
        frac = 0.6 if hi is None else 0.5
        slice_end = min(end, now + remaining * frac)
        E = _anneal(m, d, D, rng, slice_end)
        if E is not None:
            n = 2 * m
            edges = [(a, m + b) for a, b in E]
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)
                lo = m
                if hi is None:
                    step *= 2
                continue
        hi = m

    return best
