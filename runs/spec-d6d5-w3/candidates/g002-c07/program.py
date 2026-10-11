import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold direction: direct simulated annealing over simple d-regular bipartite
# graphs (no voltage group). The state is an explicit edge list between two
# sides A = 0..N-1 and B = 0..N-1. Moves are degree-preserving double-edge
# swaps, and the cost is the number of vertex pairs at distance > D.
# Only fully verified graphs are returned, and a valid fallback is always kept.
# ----------------------------------------------------------------------------

def _adj(N, E):
    """Adjacency lists of the bipartite graph; A vertex a is a, B vertex b is N + b."""
    adj = [[] for _ in range(2 * N)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    return adj


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance more than D, via bitmask balls."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal(N, d, D, E, rng, deadline):
    """Anneal double-edge swaps on E (a list of (a, b) pairs) to drive bad pairs to zero.

    Returns (E, cost). The edge list stays simple and d-regular throughout.
    """
    n = 2 * N
    es = set(E)
    cost = _bad_pairs(n, _adj(N, E), D)
    if cost == 0:
        return E, 0
    m = len(E)
    T0 = 3.0
    t_begin = time.monotonic()
    span = max(1e-3, deadline - t_begin)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t_begin) / span
        T = max(0.15, T0 * (1.0 - frac))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in es or (a2, b1) in es:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        c2 = _bad_pairs(n, _adj(N, E), D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            es.discard((a1, b1))
            es.discard((a2, b2))
            es.add((a1, b2))
            es.add((a2, b1))
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return E, cost


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = {"n": n0, "e": e0}

    def consider(n, e):
        if n > best["n"] and lib.is_valid(n, e, d, D):
            best["n"] = n
            best["e"] = e

    if D >= 3:
        # Projective plane incidence graph when d-1 is a prime power (or a smaller prime power).
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                try:
                    consider(*lib.projective_plane_incidence(q))
                except Exception:
                    pass
                break
        # Araujo-Pardo-Lopez record graph for D = 3 when d-2 is a prime power >= 3.
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                consider(*lib.araujo_lopez_graph(q))
            except Exception:
                pass

    # Main bold search: annealed simple d-regular bipartite graphs with N per side.
    bound = lib.moore_bound(d, D)
    N = best["n"] // 2 + 1
    while time.monotonic() < deadline and 2 * N <= bound and N >= d:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = now + max(2.0, 0.5 * remaining)
        S = rng.sample(range(N), d)
        E = [(i, (i + s) % N) for i in range(N) for s in S]
        E, cost = _anneal(N, d, D, E, rng, min(slice_end, deadline))
        if cost == 0:
            consider(2 * N, [(a, N + b) for a, b in E])
            N = max(N + 1, best["n"] // 2 + 1)

    if not lib.is_valid(best["n"], best["e"], d, D):
        best["n"], best["e"] = lib.haar_graph(d, range(d))
    return best["n"], best["e"]
