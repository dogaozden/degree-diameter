import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Random-regular bipartite annealing (diameter-driven, unstructured).
#
# Vertices: A-side 0..m-1 and B-side m..2m-1. The graph is d-regular bipartite,
# stored as a list E of pairs (a, b) meaning edge (a, m+b). Moves are degree-
# preserving 2-switches; the cost is the number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _adj(m, E):
    adj = [[] for _ in range(2 * m)]
    for a, b in E:
        adj[a].append(m + b)
        adj[m + b].append(a)
    return adj


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (bitmask BFS)."""
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


def _random_regular(m, d, rng):
    """Edge list of a random d-regular bipartite simple graph on m+m vertices, or None."""
    for _ in range(50):
        S = set()
        E = []
        ok = True
        for _layer in range(d):
            placed = False
            for _try in range(100):
                perm = list(range(m))
                rng.shuffle(perm)
                if all((a, perm[a]) not in S for a in range(m)):
                    placed = True
                    break
            if not placed:
                ok = False
                break
            for a in range(m):
                S.add((a, perm[a]))
                E.append((a, perm[a]))
        if ok:
            return E
    return None


def _anneal(m, d, D, E, rng, deadline, iters):
    """Degree-preserving 2-switch annealing toward diameter <= D; returns E or None."""
    n = 2 * m
    S = set(E)
    cost = _bad(n, _adj(m, E), D)
    if cost == 0:
        return E
    T0, T1 = 1.5, 0.15
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (t / max(1, iters))
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
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
        c2 = _bad(n, _adj(m, E), D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            S.discard(e1)
            S.discard(e2)
            S.add((a1, b1))
            S.add((a2, b2))
    return E if cost == 0 else None


def _largest_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _largest_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: unstructured d-regular bipartite graphs, annealed by 2-switches.
    # The side size m is raised one step at a time whenever annealing succeeds,
    # so every accepted graph strictly beats the current best order.
    m = max(d + 1, best_n // 2 + 1)
    iters = 6000
    while time.monotonic() < deadline:
        E = _random_regular(m, d, rng)
        if E is None:
            m += 1
            continue
        res = _anneal(m, d, D, E, rng, deadline, iters)
        if res is not None:
            edges = [(a, m + b) for a, b in res]
            consider(2 * m, edges)
            m += 1
            iters = 6000
        else:
            iters = min(int(iters * 1.3), 60000)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
