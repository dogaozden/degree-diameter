import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Edge-switch annealing on bipartite d-regular graphs.
#
# A graph on sides A = {0..T-1} and B = {0..T-1} is stored as a list E of
# pairs (a, b); vertex B-index b is output as T + b. Every vertex keeps its
# degree under double-edge switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), so the
# graph stays bipartite and d-regular. The cost is the number of unordered
# vertex pairs at distance > D, computed with big-int reachability bitsets.
# ----------------------------------------------------------------------------

def _bad(T, E, D):
    N = 2 * T
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(T + b)
        adj[T + b].append(a)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _anneal(T, E, D, deadline, rng):
    """Anneal E in place toward zero bad pairs; return True if it reaches zero by deadline."""
    Eset = set(E)
    cost = _bad(T, E, D)
    if cost == 0:
        return True
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)
    t0, t1 = 2.0, 0.1
    m = len(E)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        temp = t0 * (t1 / t0) ** min(1.0, (now - t_start) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        e1 = (a1, b2)
        e2 = (a2, b1)
        if e1 in Eset or e2 in Eset:
            continue
        E[i] = e1
        E[j] = e2
        Eset.discard((a1, b1))
        Eset.discard((a2, b2))
        Eset.add(e1)
        Eset.add(e2)
        c2 = _bad(T, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            Eset.discard(e1)
            Eset.discard(e2)
            Eset.add((a1, b1))
            Eset.add((a2, b2))
    return cost == 0


def _grow(T, E, d, rng):
    """Add one A-vertex and one B-vertex, preserving d-regularity.

    Pick d edges with pairwise distinct endpoints, remove them, then join the new
    A-vertex T to their B-endpoints and the new B-vertex T to their A-endpoints.
    Returns (T+1, new_E), or None if no suitable edge set was sampled.
    """
    sel = None
    for _ in range(2000):
        cand = rng.sample(range(len(E)), d)
        As = {E[i][0] for i in cand}
        Bs = {E[i][1] for i in cand}
        if len(As) == d and len(Bs) == d:
            sel = cand
            break
    if sel is None:
        return None
    chosen = set(sel)
    newE = [e for k, e in enumerate(E) if k not in chosen]
    for i in sel:
        a, b = E[i]
        newE.append((T, b))
        newE.append((a, T))
    return T + 1, newE


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Fast path: the projective plane meets the Moore bound when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Safe fallback: K_{d,d} is d-regular with diameter 2, valid for D >= 2.
    fallback = (2 * d, [(a, d + b) for a in range(d) for b in range(d)])
    best_n, best_edges = fallback

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None and pg[0] > best_n and lib.is_valid(pg[0], pg[1], d, D):
            best_n, best_edges = pg

    # Main search: grow a d-regular bipartite graph one vertex pair at a time,
    # re-annealing after each growth step. The last valid state is kept.
    deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)
    bestT = d
    bestE = [(a, b) for a in range(d) for b in range(d)]

    while time.monotonic() < deadline:
        grown = _grow(bestT, bestE, d, rng)
        if grown is None:
            break
        T, E = grown
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0:
            break
        stage = min(remaining, max(3.0, 0.25 * remaining))
        if _anneal(T, E, D, now + stage, rng):
            bestT, bestE = T, E

    if bestT > d:
        n = 2 * bestT
        edges = [(a, bestT + b) for a, b in bestE]
        if n > best_n and lib.is_valid(n, edges, d, D):
            best_n, best_edges = n, edges

    if not lib.is_valid(best_n, best_edges, d, D):
        return fallback
    return best_n, best_edges
