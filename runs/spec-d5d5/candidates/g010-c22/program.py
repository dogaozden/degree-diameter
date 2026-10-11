import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Constructions:
#   D = 2: K_{d,d} (meets the Moore bound).
#   D = 3: incidence graph of PG(2, q) when available.
#   D >= 4 (and D = 3 fallback): simulated annealing over d-regular bipartite
#   graphs using double edge swaps. The objective is the number of vertex pairs
#   at distance > D. The search grows the order one vertex per side at a time,
#   by a vertex insertion that keeps every degree exactly d. Each step is
#   annealed until the diameter condition holds, so every accepted graph is valid.
# ----------------------------------------------------------------------------


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost(n, D, ea, eb):
    """Number of unordered vertex pairs at distance > D in the bipartite graph.

    A-vertices are 0..n-1 and B-vertices are n..2n-1. Edge k joins ea[k] and n + eb[k].
    """
    N = 2 * n
    adj = [[] for _ in range(N)]
    for a, b in zip(ea, eb):
        bb = n + b
        adj[a].append(bb)
        adj[bb].append(a)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    missing = 0
    for r in reach:
        missing += N - r.bit_count()
    return missing // 2


def _anneal(n, D, ea, eb, rng, deadline):
    """Anneal double edge swaps (keeping all degrees) until the diameter condition holds.

    Modifies ea and eb in place. Returns the final cost (0 means valid).
    """
    S = {a * n + b for a, b in zip(ea, eb)}
    cur = _cost(n, D, ea, eb)
    if cur == 0:
        return 0
    E = len(ea)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0 = 1.0 + 0.1 * cur
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * max(0.0, 1.0 - (now - t0) / span) + 0.05
        i = rng.randrange(E)
        j = rng.randrange(E)
        if i == j:
            continue
        a1, b1 = ea[i], eb[i]
        a2, b2 = ea[j], eb[j]
        if a1 == a2 or b1 == b2:
            continue
        k1 = a1 * n + b2
        k2 = a2 * n + b1
        if k1 in S or k2 in S:
            continue
        eb[i] = b2
        eb[j] = b1
        c = _cost(n, D, ea, eb)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S.discard(a1 * n + b1)
            S.discard(a2 * n + b2)
            S.add(k1)
            S.add(k2)
            cur = c
        else:
            eb[i] = b1
            eb[j] = b2
    return cur


def _grow(n, d, ea, eb, rng):
    """Insert one new A-vertex and one new B-vertex, keeping all degrees equal to d.

    Pick d edges (x_i, y_i) forming a matching. Replace each by (x_i, newB) and
    add (newA, y_i). Returns (n+1, ea2, eb2), or None if no matching is found.
    """
    E = len(ea)
    order = list(range(E))
    rng.shuffle(order)
    usedA, usedB, chosen = set(), set(), []
    for idx in order:
        if ea[idx] not in usedA and eb[idx] not in usedB:
            chosen.append(idx)
            usedA.add(ea[idx])
            usedB.add(eb[idx])
            if len(chosen) == d:
                break
    if len(chosen) < d:
        return None
    newA = n
    newB = n
    ea2 = list(ea)
    eb2 = list(eb)
    for idx in chosen:
        y = eb[idx]
        eb2[idx] = newB
        ea2.append(newA)
        eb2.append(y)
    return n + 1, ea2, eb2


def _circulant(n, d, rng):
    """d-regular bipartite circulant on n + n vertices with random distinct shifts."""
    shifts = rng.sample(range(n), d)
    ea = [a for a in range(n) for _ in range(d)]
    eb = [(a + s) % n for a in range(n) for s in shifts]
    return n, ea, eb


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
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib._moore_bound(d, D)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if best[0] >= moore:
                return best

    # Generic search: grow a valid d-regular bipartite graph one vertex per side.
    moore_side = moore // 2
    bn = d
    ba = [a for a in range(d) for _ in range(d)]
    bb = [b for a in range(d) for b in range(d)]

    while bn < moore_side:
        remaining = deadline - time.monotonic()
        if remaining <= 0.5:
            break
        g = _grow(bn, d, ba, bb, rng)
        if g is None:
            g = _circulant(bn + 1, d, rng)
        n2, a2, b2 = g
        step_deadline = min(deadline, time.monotonic() + max(1.5, 0.25 * remaining))
        res = _anneal(n2, D, a2, b2, rng, step_deadline)
        if res == 0:
            edges = [(a, n2 + b) for a, b in zip(a2, b2)]
            if lib.is_valid(2 * n2, edges, d, D):
                bn, ba, bb = n2, a2, b2
                consider(2 * n2, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
