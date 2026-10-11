import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy: a direct, unstructured search. Start from a random bi-Cayley
# (Haar) graph that is d-regular and bipartite with a few more vertices than
# the current best. Then simulated annealing on edge swaps, which keep every
# degree exactly d and every edge between the two sides, minimizing the number
# of vertex pairs at distance > D. Each success grows the order by 2 and
# restarts from a new seed. Structured fallbacks (K_{d,d}, PG(2,d-1), cycles)
# are validated before use.
# ----------------------------------------------------------------------------


def _balls_bits(n, adj, D):
    """Bitmask per vertex of all vertices within distance D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return reach


def _cost(n, adj, D):
    """Number of unordered vertex pairs at distance > D (0 means valid)."""
    reach = _balls_bits(n, adj, D)
    return sum(n - r.bit_count() for r in reach) // 2


def _haar_adj(h, S):
    """Adjacency sets of the Haar graph of Z_h with connection set S (d-regular, bipartite)."""
    n, edges = lib.haar_graph(h, S)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return n, adj


def _anneal(h, D, adj, rng, deadline, T0=4.0, T1=0.3):
    """Degree-preserving edge-swap annealing. Returns True if the graph reaches diameter <= D.

    Vertices 0..h-1 form side A, h..2h-1 form side B. A swap takes edges (a,b), (c,e)
    with a, c in A and b, e in B, and replaces them with (a,e), (c,b). Degrees stay fixed
    and the graph stays bipartite.
    """
    n = 2 * h
    cur = _cost(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = T0
    it = 0
    while cur > 0:
        it += 1
        if it % 16 == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)

        a = rng.randrange(h)
        c = rng.randrange(h)
        if a == c or not adj[a] or not adj[c]:
            continue
        b = rng.choice(tuple(adj[a]))
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue

        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)

        new = _cost(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return cur == 0


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    if D == 2:
        return best

    # Projective plane incidence graph when d-1 is a prime power (diameter 3).
    q = d - 1
    if lib.is_prime_power(q):
        n_pg, e_pg = lib.projective_plane_incidence(q)
        if n_pg > best_n and lib.is_valid(n_pg, e_pg, d, D):
            best = (n_pg, e_pg)
            best_n = n_pg

    if best_n >= lib.moore_bound(d, D):
        return best

    deadline = start + 0.8 * time_limit

    # Direct annealing search, growing the order by 2 per success.
    h = best_n // 2 + 1
    while time.monotonic() < deadline and h >= d:
        now = time.monotonic()
        remaining = deadline - now
        attempt_end = min(deadline, now + max(5.0, 0.4 * remaining))

        S = [0] + rng.sample(range(1, h), d - 1)
        n, adj = _haar_adj(h, S)
        if _anneal(h, D, adj, rng, attempt_end):
            edges = [(a, b) for a in range(n) for b in adj[a] if a < b]
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
                h = n // 2 + 1
                continue
        # Failed attempt: retry at the same order with a new random start.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
