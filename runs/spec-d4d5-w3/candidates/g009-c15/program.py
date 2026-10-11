import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe base constructions.
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: bipartite 2-switch annealing on d-regular Haar starts.
#
# Start: Haar graph of Z_h with a random connection set S of size d. This is a
# simple d-regular bipartite graph on 2h vertices. Degrees are preserved by
# 2-switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keep the graph bipartite.
# The cost is the number of ordered vertex pairs at distance greater than D
# (computed with bitmask balls). Simulated annealing drives the cost to zero.
# ----------------------------------------------------------------------------

def _bad_pairs(n, adj, D):
    """Number of ordered vertex pairs at distance > D (0 means diameter <= D and connected)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal(h, d, D, rng, deadline, iters):
    """Anneal a d-regular bipartite graph on 2h vertices toward diameter <= D; None on failure."""
    n = 2 * h
    S = rng.sample(range(h), d)
    edges = [(i, h + (i + s) % h) for i in range(h) for s in S]
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    cost = _bad_pairs(n, adj, D)
    T0, T1 = 3.0, 0.3
    m = len(edges)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = edges[i]
        a2, b2 = edges[j]
        if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        # Apply the 2-switch.
        adj[a1].discard(b1); adj[b1].discard(a1)
        adj[a2].discard(b2); adj[b2].discard(a2)
        adj[a1].add(b2); adj[b2].add(a1)
        adj[a2].add(b1); adj[b1].add(a2)
        c2 = _bad_pairs(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            edges[i] = (a1, b2)
            edges[j] = (a2, b1)
        else:
            # Revert.
            adj[a1].discard(b2); adj[b2].discard(a1)
            adj[a2].discard(b1); adj[b1].discard(a2)
            adj[a1].add(b1); adj[b1].add(a1)
            adj[a2].add(b2); adj[b2].add(a2)

    if cost == 0:
        return n, [(int(a), int(b)) for a, b in edges]
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit - 1.0

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])

    moore = lib.moore_bound(d, D)
    if D < 3 or d < 3 or best_n >= moore:
        return best_n, best_e

    rng = random.Random(seed * 1000003 + d * 101 + D)
    while time.monotonic() < deadline and best_n < moore:
        h = max(d, best_n // 2 + 1)
        res = _anneal(h, d, D, rng, deadline, iters=3000)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
