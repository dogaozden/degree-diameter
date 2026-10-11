import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Reachability measure.
#
# For every vertex we keep a bitmask of the vertices within the current radius.
# Summing the unreached counts over all vertices and halving gives the number of
# unordered pairs at distance greater than D.
# ----------------------------------------------------------------------------

def _bad_pairs(n, adj, D):
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _adj_from(s, el):
    """Adjacency lists for a bipartite graph: A-vertices 0..s-1, B-vertices s..2s-1."""
    adj = [[] for _ in range(2 * s)]
    for a, b in el:
        bb = b + s
        adj[a].append(bb)
        adj[bb].append(a)
    return adj


# ----------------------------------------------------------------------------
# New construction: edge-switch annealing on d-regular bipartite graphs.
#
# Start from a random Haar-type d-regular bipartite graph on sides of size s
# (A_i joined to B_{i+t} for d distinct shifts t). Repeatedly apply degree-
# preserving edge switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), accepting by a
# Metropolis rule on the number of bad pairs. Once the cost reaches zero, the
# side size s is increased and the search restarts from a fresh start.
# This is unlike the group-voltage lifts used previously: it searches the full
# space of d-regular bipartite graphs on 2s vertices.
# ----------------------------------------------------------------------------

def _anneal(d, D, s, rng, deadline):
    shifts = rng.sample(range(s), d)
    el = [(i, (i + t) % s) for i in range(s) for t in shifts]
    E = set(el)
    m = len(el)
    adj = _adj_from(s, el)
    cost = _bad_pairs(2 * s, adj, D)

    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 2.0, 0.1

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - t0) / span)
        T = T0 * (T1 / T0) ** frac

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = el[i]
        a2, b2 = el[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in E or (a2, b1) in E:
            continue

        n1 = (a1, b2)
        n2 = (a2, b1)
        E.discard((a1, b1))
        E.discard((a2, b2))
        E.add(n1)
        E.add(n2)
        el[i] = n1
        el[j] = n2

        c2 = _bad_pairs(2 * s, _adj_from(s, el), D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            E.discard(n1)
            E.discard(n2)
            E.add((a1, b1))
            E.add((a2, b2))
            el[i] = (a1, b1)
            el[j] = (a2, b2)

    if cost == 0:
        return el
    return None


# ----------------------------------------------------------------------------
# Small safe bases.
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    moore = lib.moore_bound(d, D)

    # Edge-switch annealing for side size s, climbing one side at a time.
    if D >= 3 and d >= 3 and best_n < moore:
        rng = random.Random(seed * 1000003 + d * 31 + D)
        s = max(d, best_n // 2 + 1)
        fails = 0
        while 2 * s <= moore:
            remaining = deadline - time.monotonic()
            if remaining <= 0.5:
                break
            budget = min(remaining, max(3.0, 0.35 * remaining))
            el = _anneal(d, D, s, rng, time.monotonic() + budget)
            if el is None:
                fails += 1
                if fails >= 2:
                    break
                continue
            fails = 0
            n = 2 * s
            edges = [(a, s + b) for a, b in el]
            if lib.is_valid(n, edges, d, D):
                consider(n, edges)
            else:
                break
            s += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
