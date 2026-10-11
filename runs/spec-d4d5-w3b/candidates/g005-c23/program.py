import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe fallbacks: K_{d,d} (diameter 2) and the projective plane incidence graph
# (diameter 3). Both are validated before use.
# ----------------------------------------------------------------------------

def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _fallback(d, D):
    cands = [lib.haar_graph(d, range(d))]
    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            cands.append(pg)
    valid = [c for c in cands if lib.is_valid(c[0], c[1], d, D)]
    if not valid:
        return (2, [(0, 1)])
    return max(valid, key=lambda c: c[0])


# ----------------------------------------------------------------------------
# New construction: direct annealing over bipartite graphs with max degree d.
#
# State: a bipartite graph with sides A = {0..s-1} and B = {0..s-1}, edges
# stored as (a, b) pairs with degree <= d on every vertex. Cost = number of
# ordered vertex pairs at distance > D (zero means diameter <= D).
# Moves: add an edge, delete an edge, or switch two edges (keeps degrees).
# Whenever cost reaches zero the side size grows by one, and the search
# continues from the valid graph with the new isolated vertices.
# ----------------------------------------------------------------------------

def _cost(s, D, E):
    """Ordered count of vertex pairs not within distance D (0 iff valid)."""
    n = 2 * s
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(s + b)
        adj[s + b].append(a)
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
    return sum(n - r.bit_count() for r in reach)


def _load(s, edges):
    """Build the mutable state (edge list, edge set, A-degrees, B-degrees) for side size s."""
    E = list(edges)
    S = set(E)
    dA = [0] * s
    dB = [0] * s
    for a, b in E:
        dA[a] += 1
        dB[b] += 1
    return E, S, dA, dB


def _apply(E, S, dA, dB, rem, add):
    for a, b in rem:
        E.remove((a, b))
        S.discard((a, b))
        dA[a] -= 1
        dB[b] -= 1
    for a, b in add:
        E.append((a, b))
        S.add((a, b))
        dA[a] += 1
        dB[b] += 1


def _propose(s, d, E, S, dA, dB, rng):
    """Random move as (removed_edges, added_edges), or None if no move was drawn."""
    r = rng.random()
    if r < 0.35:
        for _ in range(20):
            a = rng.randrange(s)
            b = rng.randrange(s)
            if dA[a] < d and dB[b] < d and (a, b) not in S:
                return [], [(a, b)]
        return None
    if r < 0.45:
        if not E:
            return None
        return [rng.choice(E)], []
    if len(E) < 2:
        return None
    e1 = rng.choice(E)
    e2 = rng.choice(E)
    a1, b1 = e1
    a2, b2 = e2
    if a1 == a2 or b1 == b2:
        return None
    if (a1, b2) in S or (a2, b1) in S:
        return None
    return [e1, e2], [(a1, b2), (a2, b1)]


def _anneal(s, d, D, edges, rng, deadline):
    """Anneal at fixed side size s; returns (best_cost, best_edges)."""
    E, S, dA, dB = _load(s, edges)
    cost = _cost(s, D, E)
    best_cost, best_E = cost, list(E)
    T0, T1 = 6.0, 0.3
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        mv = _propose(s, d, E, S, dA, dB, rng)
        if mv is None:
            continue
        rem, add = mv
        _apply(E, S, dA, dB, rem, add)
        c2 = _cost(s, D, E)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_E = list(E)
        else:
            _apply(E, S, dA, dB, add, rem)
    return best_cost, best_E


def _search(d, D, rng, deadline, best, s0, budget):
    """Grow a valid bipartite graph by annealing; returns the best valid (n, edges) found."""
    s = s0
    edges = []
    chunk = max(2.0, 0.25 * budget)
    while time.monotonic() < deadline:
        chunk_end = min(deadline, time.monotonic() + chunk)
        cost, best_E = _anneal(s, d, D, edges, rng, chunk_end)
        if cost == 0:
            n_c = 2 * s
            cand_edges = [(a, s + b) for a, b in best_E]
            if n_c > best[0] and lib.is_valid(n_c, cand_edges, d, D):
                best = (n_c, cand_edges)
            edges = best_E
            s += 1
        else:
            edges = best_E
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []

    best = _fallback(d, D)

    # Only D >= 4 with d >= 2 uses the annealing construction; the projective
    # plane fallback already covers the diameter-3 calibration case.
    if D < 4 or d < 2:
        return best

    rng = random.Random(seed * 1000003 + d * 31 + D)
    mo = lib.moore_bound(d, D)
    s0 = max(best[0] // 2, mo // 4, d)

    try:
        best = _search(d, D, rng, deadline, best, s0, budget)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d, D)
    return best
