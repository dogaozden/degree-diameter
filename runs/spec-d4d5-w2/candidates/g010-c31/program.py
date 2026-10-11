import math
import random
import time

import lib


def _pg_candidate(d):
    """Incidence graph of PG(2, d-1) when d-1 is a prime power (diameter 3, degree d)."""
    if d - 1 < 2 or not lib.is_prime_power(d - 1):
        return None
    return lib.projective_plane_incidence(d - 1)


def _ball_cost(h, edges, D):
    """Number of ordered vertex pairs not within distance D (0 means diameter <= D).

    Vertices 0..h-1 form side A; h..2h-1 form side B. Every edge is (a, b) with b >= h.
    """
    n = 2 * h
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = reach[:]
        for u, v in edges:
            new[u] |= reach[v]
            new[v] |= reach[u]
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal_bipartite(h, d, D, rng, deadline):
    """Edge-swap simulated annealing on a d-regular bipartite graph with h + h vertices.

    Start: Haar graph (always simple and d-regular). Moves: swap the B-ends of two
    edges, which keeps every degree at d and the graph bipartite. Cost: unreached pairs.
    Returns a list of edges if a diameter-<=D graph is found before the deadline, else None.
    """
    E = [[a, h + (a + s) % h] for a in range(h) for s in range(d)]
    present = {(a, b) for a, b in E}
    m = len(E)
    cur = _ball_cost(h, E, D)
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    T0, T1 = 2.0, 0.15

    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t_start) / span
        T = T0 * (T1 / T0) ** frac

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in present or (a2, b1) in present:
            continue

        E[i] = [a1, b2]
        E[j] = [a2, b1]
        c2 = _ball_cost(h, E, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            present.discard((a1, b1))
            present.discard((a2, b2))
            present.add((a1, b2))
            present.add((a2, b1))
            cur = c2
        else:
            E[i] = [a1, b1]
            E[j] = [a2, b2]

    if cur == 0:
        return [(a, b) for a, b in E]
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Bold change: direct annealing over bipartite edge swaps, no algebraic base.
    # Try to find a d-regular bipartite graph with 2h vertices, increasing h on success.
    if D >= 3 and d >= 3:
        moore = lib.moore_bound(d, D)
        h = max(d, best_n // 2 + 1)
        while time.monotonic() < deadline and 2 * h <= moore:
            now = time.monotonic()
            remaining = deadline - now
            attempt_deadline = min(deadline, now + max(2.0, 0.6 * remaining))
            E = _anneal_bipartite(h, d, D, rng, attempt_deadline)
            if E is not None:
                consider(2 * h, E)
                h = max(h + 1, best_n // 2 + 1)
            # On failure, retry the same h from a fresh start.

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
