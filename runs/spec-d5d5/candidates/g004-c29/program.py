import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Unstructured search: start from K_{d,d} and grow a d-regular bipartite graph
# one vertex per side at a time. Each growth step splits d edges through the
# new pair, which keeps every degree at d and the graph bipartite. Then a
# double-edge-switch simulated annealing removes all pairs at distance > D.
# Cost = number of ordered vertex pairs not within distance D.
# ----------------------------------------------------------------------------

def _unreached(N, E, D):
    """Ordered pairs (x, y) with dist(x, y) > D. Vertices: A = i, B = N + j."""
    n = 2 * N
    adj = [[] for _ in range(n)]
    for i, j in E:
        b = N + j
        adj[i].append(b)
        adj[b].append(i)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return n * n - sum(r.bit_count() for r in reach)


def _grow(N, E, d, rng):
    """Add one A vertex N and one B vertex N, keeping all degrees equal to d.

    Pick d edges (i, j) with distinct i and distinct j. Replace each with
    (i, N) and (N, j). Returns (N + 1, new_edges), or None if no such matching.
    """
    order = list(range(len(E)))
    rng.shuffle(order)
    used_i, used_j, chosen = set(), set(), []
    for idx in order:
        i, j = E[idx]
        if i in used_i or j in used_j:
            continue
        used_i.add(i)
        used_j.add(j)
        chosen.append(idx)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    drop = set(chosen)
    newE = [E[k] for k in range(len(E)) if k not in drop]
    for idx in chosen:
        i, j = E[idx]
        newE.append((i, N))
        newE.append((N, j))
    return N + 1, newE


def _anneal(N, E, D, rng, deadline):
    """Double-edge-switch annealing on E (modified in place). True if cost reaches 0."""
    Eset = set(E)
    cost = _unreached(N, E, D)
    if cost == 0:
        return True
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = 2.0
    m = len(E)
    it = 0
    while cost > 0:
        it += 1
        if (it & 7) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = (now - t0) / span
            T = 2.0 * (0.05) ** frac  # cools from 2.0 to 0.1
        p = rng.randrange(m)
        q = rng.randrange(m)
        if p == q:
            continue
        i1, j1 = E[p]
        i2, j2 = E[q]
        if i1 == i2 or j1 == j2:
            continue
        if (i1, j2) in Eset or (i2, j1) in Eset:
            continue
        E[p] = (i1, j2)
        E[q] = (i2, j1)
        Eset.discard((i1, j1))
        Eset.discard((i2, j2))
        Eset.add((i1, j2))
        Eset.add((i2, j1))
        c2 = _unreached(N, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            E[p] = (i1, j1)
            E[q] = (i2, j2)
            Eset.discard((i1, j2))
            Eset.discard((i2, j1))
            Eset.add((i1, j1))
            Eset.add((i2, j2))
    return cost == 0


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, always valid.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    # D = 3 with d - 1 a prime power: projective plane incidence is Moore-optimal.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    moore = lib._moore_bound(d, D)
    Nb = d
    Eb = [(i, j) for i in range(d) for j in range(d)]

    while time.monotonic() < deadline and 2 * (Nb + 1) <= moore:
        res = _grow(Nb, Eb, d, rng)
        if res is None:
            break
        N, E = res
        now = time.monotonic()
        slice_end = min(deadline, now + max(3.0, 0.3 * budget))
        if _anneal(N, E, D, rng, slice_end):
            edges = [(i, N + j) for i, j in E]
            if lib.is_valid(2 * N, edges, d, D):
                Nb, Eb = N, E
                best = (2 * N, edges)
            else:
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
