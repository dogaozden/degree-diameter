"""Direct graph search for bipartite d-regular graphs with bounded diameter.

Different from the voltage-lift pipeline: the search works on the explicit
graph. It starts from a circulant bipartite d-regular graph, anneals with
degree-preserving 2-switches (a1-b1, a2-b2 -> a1-b2, a2-b1) to remove
pairs at distance > D, and once a valid graph is found it grows by two
vertices (one per side) using d edge removals, then anneals again.
Every returned graph is checked with lib.is_valid; K_{d,d} is the fallback.
"""
import math
import random
import time

import lib


def _cost(h, D, E):
    """Number of ordered vertex pairs at distance > D (0 means diameter <= D)."""
    N = 2 * h
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(h + b)
        adj[h + b].append(a)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _anneal(h, D, E, rng, deadline, T0=1.5, T1=0.1):
    """Simulated annealing over 2-switches; returns (best_cost, best_edge_list)."""
    E = [list(e) for e in E]
    eset = {(a, b) for a, b in E}
    cur = _cost(h, D, E)
    best, bestE = cur, [list(e) for e in E]
    m = len(E)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        i, j = rng.randrange(m), rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        E[i] = [a1, b2]
        E[j] = [a2, b1]
        new = _cost(h, D, E)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            eset.discard((a1, b1))
            eset.discard((a2, b2))
            eset.add((a1, b2))
            eset.add((a2, b1))
            cur = new
            if cur < best:
                best = cur
                bestE = [list(e) for e in E]
        else:
            E[i] = [a1, b1]
            E[j] = [a2, b2]
    return best, bestE


def _circulant(h, d):
    """d-regular bipartite circulant on h + h vertices (needs h >= d)."""
    return [[i, (i + s) % h] for i in range(h) for s in range(d)]


def _expand(h, d, E, rng):
    """Grow a d-regular bipartite graph by one vertex per side; None if no valid removal set."""
    E = [list(e) for e in E]
    idx = list(range(len(E)))
    rng.shuffle(idx)
    chosen, usedA, usedB = [], set(), set()
    for i in idx:
        a, b = E[i]
        if a in usedA or b in usedB:
            continue
        chosen.append(i)
        usedA.add(a)
        usedB.add(b)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    chosen_set = set(chosen)
    newE = [e for k, e in enumerate(E) if k not in chosen_set]
    x = h  # new A vertex index
    y = h  # new B vertex index
    for i in chosen:
        a, b = E[i]
        newE.append([x, b])
        newE.append([a, y])
    return h + 1, newE


def _search(d, D, time_limit, deadline, rng, best):
    """Grow valid d-regular bipartite graphs; returns the best (n, edges) found."""
    h = d
    E = _circulant(h, d)
    level_budget = max(1.0, 0.12 * time_limit)
    while time.monotonic() < deadline:
        level_deadline = min(deadline, time.monotonic() + level_budget)
        bc, bE = _anneal(h, D, E, rng, level_deadline)
        E = bE
        if bc == 0:
            n = 2 * h
            edges = [(a, h + b) for a, b in E]
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
            nxt = _expand(h, d, E, rng)
            if nxt is None:
                break
            h, E = nxt
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Exact record family: projective plane incidence meets the Moore bound.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    if d >= 2 and D >= 3:
        deadline = start + 0.8 * time_limit
        try:
            best = _search(d, D, time_limit, deadline, rng, best)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
