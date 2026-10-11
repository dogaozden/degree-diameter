import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic baselines (exact small cases).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New idea: degree-preserving 2-switch annealing on balanced bipartite graphs
# with d-regular sides, plus a degree-preserving "edge split" growth move.
#
# State: m vertices per side, E = list of [a, b] with a, b in 0..m-1 (A index, B index),
# ex = set of (a, b) pairs for fast membership. Every vertex keeps degree exactly d.
#
#  * 2-switch: edges (a1,b1),(a2,b2) become (a1,b2),(a2,b1). Degrees unchanged.
#  * Split growth: add one new A vertex and one new B vertex. Each of d rounds picks
#    an edge (a,b), replaces it by (a,b_new) and adds (a_new,b). Degrees are all
#    preserved, and the new vertices reach degree exactly d without touching the rest.
#  * Cost = number of ordered-unimportant unordered pairs farther than D apart.
# The search grows m adaptively: a step that anneals to cost 0 is kept, otherwise
# the step shrinks and the best valid state is restored.
# ----------------------------------------------------------------------------

def _haar_start(m, d, rng):
    """d-regular bipartite start: Haar graph of Z_m with a random connection set of size d."""
    S = rng.sample(range(m), d)
    return [[i, (i + s) % m] for i in range(m) for s in S]


def _adj_lists(m, E):
    """Unified adjacency: A index a -> vertex a, B index b -> vertex m + b."""
    adj = [[] for _ in range(2 * m)]
    for a, b in E:
        bb = m + b
        adj[a].append(bb)
        adj[bb].append(a)
    return adj


def _bad_pairs_fast(n, adj, D):
    """Sum over vertices of the number of vertices not within distance D (bitmask BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal(m, D, E, ex, deadline, rng):
    """Anneal with 2-switches until cost 0 or the deadline. Returns the final cost."""
    n = 2 * m
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    cost = _bad_pairs_fast(n, _adj_lists(m, E), D)
    L = len(E)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = max(0.15, 2.0 * (1.0 - (now - t0) / span))
        i = rng.randrange(L)
        j = rng.randrange(L)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if (a1, b2) in ex or (a2, b1) in ex:
            continue
        ex.discard((a1, b1))
        ex.discard((a2, b2))
        ex.add((a1, b2))
        ex.add((a2, b1))
        E[i] = [a1, b2]
        E[j] = [a2, b1]
        c2 = _bad_pairs_fast(n, _adj_lists(m, E), D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            ex.discard((a1, b2))
            ex.discard((a2, b1))
            ex.add((a1, b1))
            ex.add((a2, b2))
            E[i] = [a1, b1]
            E[j] = [a2, b2]
    return cost


def _split(m, d, E, ex, k, rng):
    """Degree-preserving growth by k new A/B vertex pairs. Returns new m, or None on failure."""
    for _ in range(k):
        an = m
        bn = m
        m += 1
        for _t in range(d):
            ok = False
            for _try in range(400):
                i = rng.randrange(len(E))
                a, b = E[i]
                if (an, b) not in ex and (a, bn) not in ex:
                    ok = True
                    break
            if not ok:
                return None
            ex.discard((a, b))
            ex.add((a, bn))
            E[i] = [a, bn]
            ex.add((an, b))
            E.append([an, b])
    return m


def _search(d, D, deadline, rng):
    """Find a valid balanced bipartite d-regular graph, then grow it by splits.

    Returns (m, E) for the largest valid state found, or None.
    """
    m = max(d + 1, 4 * d)
    E = None
    found = False
    while time.monotonic() < deadline:
        E = _haar_start(m, d, rng)
        ex = {(a, b) for a, b in E}
        att = min(deadline, time.monotonic() + 3.0)
        if _anneal(m, D, E, ex, att, rng) == 0:
            found = True
            break
        m = max(d + 1, m - 3)
    if not found:
        return None

    best_m = m
    best_E = [list(x) for x in E]
    step = 1
    while time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        budget = min(remaining, max(1.5, 0.12 * remaining))
        E2 = [list(x) for x in best_E]
        ex2 = {(a, b) for a, b in E2}
        m2 = _split(best_m, d, E2, ex2, step, rng)
        if m2 is None:
            step = 1
            continue
        cost = _anneal(m2, D, E2, ex2, min(deadline, now + budget), rng)
        if cost == 0:
            best_m, best_E = m2, E2
            step = min(step * 2, max(1, best_m // 20))
        else:
            step = max(1, step // 2)
    return best_m, best_E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    target = lib.moore_bound(d, D)
    if best_n >= target:
        return best

    if D >= 3 and d >= 2:
        res = _search(d, D, deadline, rng)
        if res is not None:
            m, E = res
            edges = [(a, m + b) for a, b in E]
            consider(2 * m, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
