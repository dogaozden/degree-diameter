import math
import random
import time

import lib


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitset BFS, all sources at once)."""
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


def _anneal(h, d, D, rng, deadline):
    """Edge-swap annealing on a d-regular bipartite graph with h + h vertices.

    Start from a Haar graph (distinct shifts, so it is simple and d-regular).
    A move swaps the B-endpoints of two edges, which preserves all degrees and
    bipartiteness. Cost is the number of vertex pairs at distance > D.
    The temperature follows the elapsed fraction of the attempt budget.
    """
    n = 2 * h
    shifts = rng.sample(range(h), d)
    E = [[a, (a + s) % h] for a in range(h) for s in shifts]
    occ = {(a, b) for a, b in E}
    m = len(E)

    def cost(edges):
        adj = [[] for _ in range(n)]
        for a, b in edges:
            adj[a].append(h + b)
            adj[h + b].append(a)
        return _bad_pairs(n, adj, D)

    c = cost(E)
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)
    T0, T1 = 1.0, 0.05

    while c > 0:
        now = time.monotonic()
        if now > deadline:
            break
        frac = min(1.0, (now - t_start) / span)
        T = T0 * (T1 / T0) ** frac

        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in occ or (a2, b1) in occ:
            continue
        E[i] = [a1, b2]
        E[j] = [a2, b1]
        c2 = cost(E)
        delta = c2 - c
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            occ.discard((a1, b1))
            occ.discard((a2, b2))
            occ.add((a1, b2))
            occ.add((a2, b1))
            c = c2
        else:
            E[i] = [a1, b1]
            E[j] = [a2, b2]

    if c == 0:
        return n, [(a, h + b) for a, b in E]
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5 * time_limit, min(0.85 * time_limit, time_limit - 3.0))
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D <= 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    def consider(n, e):
        nonlocal best, best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    # Projective plane incidence graph (diameter 3) when d - 1 is a prime power.
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        pn, pe = lib.projective_plane_incidence(q)
        consider(pn, pe)

    # Main family: bipartite d-regular graphs found by edge-swap annealing
    # directly on the graph (not via voltage lifts). Order grows whenever
    # an attempt succeeds, and backs off toward the last success on failure.
    total = max(1e-6, deadline - time.monotonic())
    attempt_budget = max(2.0, 0.12 * total)

    best_h = max(d, best[0] // 2)
    h = best_h + max(1, best_h // 25)

    while time.monotonic() < deadline:
        attempt_end = min(deadline, time.monotonic() + attempt_budget)
        res = _anneal(h, d, D, rng, attempt_end)
        if res is not None:
            consider(res[0], res[1])
            if res[0] // 2 > best_h:
                best_h = res[0] // 2
            h = h + max(1, h // 25)
        else:
            gap = h - best_h
            h = best_h + max(1, gap // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
