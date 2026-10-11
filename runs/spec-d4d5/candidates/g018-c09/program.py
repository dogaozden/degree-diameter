import math
import random
import time

import lib


# Strategy: a different family from the parent's voltage lifts and cover growth.
# Start from a bipartite circulant (Haar) d-regular graph of growing side size h,
# then run degree-preserving 2-switch simulated annealing on the edge set, with
# cost = number of vertex pairs at distance greater than D. The first h that reaches
# cost 0 is validated and kept, and the search moves on to h + 1.
# Safe fallbacks: K_{d,d} always, and the projective plane when D == 3.


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost(h, E, D):
    """Number of unordered vertex pairs at distance > D in the bipartite graph with edges E (a, b) on sides [0,h) and [h,2h)."""
    n = 2 * h
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(h + b)
        adj[h + b].append(a)
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _anneal(d, D, h, rng, deadline):
    """Simulated annealing over 2-switches of a d-regular bipartite graph on h + h vertices.

    Returns the edge list E (pairs (a, b), a and b local indices) if cost 0 is reached
    before the deadline, otherwise None.
    """
    S = rng.sample(range(h), d)
    E = [(a, (a + s) % h) for a in range(h) for s in S]
    P = set(E)
    m = len(E)
    cost = _cost(h, E, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 1.5, 0.05

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)

        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        e1 = (a1, b2)
        e2 = (a2, b1)
        if e1 in P or e2 in P:
            continue

        E[i] = e1
        E[j] = e2
        P.discard((a1, b1))
        P.discard((a2, b2))
        P.add(e1)
        P.add(e2)

        c2 = _cost(h, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            P.discard(e1)
            P.discard(e2)
            P.add((a1, b1))
            P.add((a2, b2))

    return E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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
    if D == 2 or best_n >= moore:
        return best

    # Main search: grow the side size h and anneal a d-regular bipartite graph to diameter D.
    h = max(d, best_n // 2 + 1)
    while time.monotonic() < deadline and 2 * h <= moore:
        remaining = deadline - time.monotonic()
        budget = max(2.0, 0.5 * remaining)
        att_deadline = min(deadline, time.monotonic() + budget)
        E = _anneal(d, D, h, rng, att_deadline)
        if E is not None:
            edges = [(a, h + b) for a, b in E]
            consider(2 * h, edges)
            h = max(h + 1, best_n // 2 + 1)
        # On failure, retry the same h from a fresh random start.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
