"""Degree-diameter search by annealed edge rewiring on bipartite regular graphs.

Strategy:
  * Baselines: K_{d,d} (diameter 2) and, for D = 3 with d-1 a prime power, the
    projective-plane incidence graph (Moore graph). Both are checked with lib.is_valid.
  * Main search: a d-regular bipartite graph with n vertices per side, started from a
    cyclic Haar graph and improved by double-edge swaps. The cost is the number of ordered
    vertex pairs at distance > D, computed with Python-int bitsets. Swaps preserve
    regularity and bipartiteness. Each success raises n, and the step size halves on failure.
  * Every returned graph is verified with lib.is_valid. The fallback is always a valid graph.
"""
import math
import random
import time

import lib


def _bad(V, adj, D):
    """Number of ordered vertex pairs at distance > D (zero iff diameter <= D)."""
    reach = [1 << v for v in range(V)]
    for _ in range(D):
        new = [0] * V
        for v in range(V):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return V * V - sum(r.bit_count() for r in reach)


def _swap(E, adj, S, n, i, j, a1, b1, a2, b2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). A-side ids are a, B-side ids are n+b."""
    S.discard((a1, b1))
    S.discard((a2, b2))
    S.add((a1, b2))
    S.add((a2, b1))
    A1, A2 = a1, a2
    B1, B2 = n + b1, n + b2
    x = adj[A1]
    x[x.index(B1)] = B2
    x = adj[A2]
    x[x.index(B2)] = B1
    x = adj[B1]
    x[x.index(A1)] = A2
    x = adj[B2]
    x[x.index(A2)] = A1
    E[i] = (a1, b2)
    E[j] = (a2, b1)


def _anneal(n, d, D, rng, deadline):
    """Try to find a d-regular bipartite graph with n vertices per side and diameter <= D.

    Returns the edge list E of (a, b) pairs with a, b in 0..n-1, or None on timeout.
    """
    V = 2 * n
    shifts = rng.sample(range(n), d)
    E = [(i, (i + s) % n) for s in shifts for i in range(n)]
    adj = [[] for _ in range(V)]
    for a, b in E:
        adj[a].append(n + b)
        adj[n + b].append(a)
    S = set(E)
    cost = _bad(V, adj, D)
    if cost == 0:
        return E

    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 8.0, 0.5
    M = len(E)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        _swap(E, adj, S, n, i, j, a1, b1, a2, b2)
        c2 = _bad(V, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _swap(E, adj, S, n, i, j, a1, b2, a2, b1)  # revert
    if cost == 0:
        return E
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 1:
        consider(2, [(0, 1)])
        return best

    # K_{d,d}: diameter 2, a safe valid fallback for every D >= 2.
    consider(*lib.haar_graph(d, range(d)))
    if D == 2:
        return best

    # Moore graph for D = 3 when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    moore = lib.moore_bound(d, D)
    if d < 3 or best[0] >= moore:
        return best

    # Annealed search for d-regular bipartite graphs with growing n per side.
    step = 1
    try:
        while time.monotonic() < deadline:
            n_try = best[0] // 2 + step
            if n_try > moore // 2:
                break
            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0.1:
                break
            att = min(remaining, max(3.0, 0.35 * remaining))
            E = _anneal(n_try, d, D, rng, now + att)
            if E is not None:
                edges = [(a, n_try + b) for a, b in E]
                consider(2 * n_try, edges)
                step = min(step * 2, 64)
            else:
                step = max(1, step // 2)
    except Exception:
        pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
