"""Exploratory family: annealed regular bipartite graphs via edge switches.

Instead of lifting or extending a structured base, this program searches
directly over d-regular bipartite graphs on a fixed number of vertices. The
state is a simple bipartite graph with sides A = [0, s) and B = [s, 2s). A move
swaps two edges (a1,b1),(a2,b2) into (a1,b2),(a2,b1). This keeps the graph
d-regular and bipartite. The cost is the number of ordered vertex pairs at
distance greater than D, computed with big-int bitsets. Simulated annealing
runs until the cost reaches zero, and the largest valid order found is kept.

Fallbacks: K_{d,d}, the projective plane incidence graph when d-1 is a prime
power and D >= 3, and any other valid graph found along the way. Every
candidate is checked with lib.is_valid before it is accepted.
"""
import math
import random
import time

import lib


def _bad_pairs(n, adj, D):
    """Number of ordered vertex pairs at distance > D (unreachable counts)."""
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


def _anneal_regular(s, d, D, deadline, rng):
    """Anneal a d-regular bipartite graph with sides of size s. Return (n, edges) or None."""
    n = 2 * s
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)

    # Circulant start: A-vertex i joins B-vertices s + (i + t) mod s for t in a random difference set.
    diffs = rng.sample(range(s), d)
    adj = [set() for _ in range(n)]
    E = []
    for i in range(s):
        for t in diffs:
            j = s + (i + t) % s
            adj[i].add(j)
            adj[j].add(i)
            E.append([i, j])

    cost = _bad_pairs(n, adj, D)
    T0, T1 = 8.0, 0.3
    m = len(E)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - t_start) / span)
        T = T0 * (T1 / T0) ** frac

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if b2 in adj[a1] or b1 in adj[a2]:
            continue

        # Apply the switch.
        adj[a1].discard(b1)
        adj[b1].discard(a1)
        adj[a2].discard(b2)
        adj[b2].discard(a2)
        adj[a1].add(b2)
        adj[b2].add(a1)
        adj[a2].add(b1)
        adj[b1].add(a2)

        c2 = _bad_pairs(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            E[i] = [a1, b2]
            E[j] = [a2, b1]
        else:
            # Revert.
            adj[a1].discard(b2)
            adj[b2].discard(a1)
            adj[a2].discard(b1)
            adj[b1].discard(a2)
            adj[a1].add(b1)
            adj[b1].add(a1)
            adj[a2].add(b2)
            adj[b2].add(a2)

    if cost == 0:
        return n, [(a, b) for a, b in E]
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.9 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = [2 * d, lib.haar_graph(d, range(d))[1]]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    # Projective plane incidence graph: diameter 3, degree q+1 = d when d-1 is a prime power.
    if D >= 3 and lib.is_prime_power(d - 1):
        n_pg, e_pg = lib.projective_plane_incidence(d - 1)
        consider(n_pg, e_pg)

    # Main search: annealed regular bipartite graphs, sides of size s.
    # Start from a size near the bound and keep trying one size above the best found.
    s0 = max(d, int(0.34 * lib.moore_bound(d, D)))
    best_s = None
    target = s0
    while time.monotonic() < end and target >= d:
        left = end - time.monotonic()
        dl = time.monotonic() + min(left, max(8.0, 0.3 * left))
        res = _anneal_regular(target, d, D, dl, rng)
        if res is not None:
            consider(res[0], res[1])
            best_s = target
            target += 1
        else:
            if best_s is None:
                target -= 2
            # If a larger size already succeeded, keep retrying the next size with fresh restarts.

    n, e = best
    if not lib.is_valid(n, e, d, D):
        n, e = lib.haar_graph(d, range(d))
    return n, e
