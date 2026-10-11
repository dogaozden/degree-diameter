import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bipartite double-edge-swap annealing.
#
# Work with d-regular bipartite graphs on sides A = {0..h-1} and B = {0..h-1}.
# A "double swap" replaces edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). It keeps
# all degrees and bipartiteness. The energy is the number of unordered vertex
# pairs at distance > D, computed by bitset ball growth. Simulated annealing
# drives the energy to zero. The order h is then increased one step at a time,
# so each success warm-climbs to a larger graph.
# ----------------------------------------------------------------------------


def _adj_from(h, E):
    """Adjacency lists for the bipartite graph with edge list E of (a, b) pairs, a and b in 0..h-1."""
    adj = [[] for _ in range(2 * h)]
    for a, b in E:
        adj[a].append(h + b)
        adj[h + b].append(a)
    return adj


def _cost(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (0 means diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal(h, d, D, rng, end):
    """Anneal a d-regular bipartite graph on 2h vertices to diameter <= D.

    Starts from a random Haar-type graph with d distinct shifts, then applies double
    edge swaps. Returns the edge list E of (a, b) pairs, or None if time runs out.
    """
    n = 2 * h
    shifts = rng.sample(range(h), d)
    E = [(i, (i + s) % h) for i in range(h) for s in shifts]
    S = set(E)
    m = len(E)
    cur = _cost(n, _adj_from(h, E), D)
    t0 = time.monotonic()
    span = max(1e-3, end - t0)
    T0, T1 = 1.0, 0.08
    while cur > 0:
        now = time.monotonic()
        if now >= end:
            return None
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        e1 = (a1, b2)
        e2 = (a2, b1)
        if e1 in S or e2 in S:
            continue
        E[i] = e1
        E[j] = e2
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add(e1)
        S.add(e2)
        c2 = _cost(n, _adj_from(h, E), D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            S.discard(e1)
            S.discard(e2)
            S.add((a1, b1))
            S.add((a2, b2))
    return E


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe baseline: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    # D = 3: projective plane incidence when d - 1 is a prime power.
    if D == 3:
        for q in range(min(d - 1, 40), 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                break

    rng = random.Random(seed * 1000003 + 97 * d + D)

    # Sweep the side size h upward from a size that anneals reliably.
    h = max(d, min(150, moore // 4))
    while time.monotonic() < deadline and 2 * h <= moore:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(2.0, 0.35 * remaining))
        E = _anneal(h, d, D, rng, slice_end)
        if E is None:
            continue  # retry the same h from a fresh random start
        n = 2 * h
        edges = [(a, h + b) for a, b in E]
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
        h += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
