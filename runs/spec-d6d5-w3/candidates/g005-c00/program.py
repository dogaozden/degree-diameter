import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic baselines (D = 3): projective plane incidence and Araujo-Pardo-Lopez.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# NEW: switch-annealing for d-regular bipartite graphs with a prescribed diameter.
#
# Every state is a d-regular bipartite graph on h + h vertices (A = 0..h-1,
# B = h..2h-1). A "switch" takes two edges (a1,b1), (a2,b2) and replaces them
# by (a1,b2), (a2,b1). Switches keep every degree and the bipartition, so the
# degree bound is never violated. The cost is the number of ordered pairs at
# distance > D, computed with big-int reachability bitmasks. Metropolis
# acceptance with a geometric cooling schedule drives the cost to zero.
# Starts are random d-regular bipartite graphs or Haar graphs (cyclic lifts).
# ----------------------------------------------------------------------------

def _ball_bad(n, adj, D):
    """Sum over vertices of the number of vertices at distance > D (ordered pairs)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _swap_apply(E, adj, eset, n, i, a, b):
    """Replace edge number i by (a, b), updating adjacency lists and the edge-key set."""
    oa, ob = E[i]
    eset.discard(oa * n + ob)
    adj[oa].remove(ob)
    adj[ob].remove(oa)
    E[i] = (a, b)
    eset.add(a * n + b)
    adj[a].append(b)
    adj[b].append(a)


def _random_regular(h, d, rng):
    """Union of d random perfect matchings between A and B (simple), or None."""
    n = 2 * h
    E = []
    eset = set()
    for _ in range(d):
        ok = False
        for _ in range(2000):
            p = list(range(h))
            rng.shuffle(p)
            if all(i * n + h + p[i] not in eset for i in range(h)):
                ok = True
                break
        if not ok:
            return None
        for i in range(h):
            E.append((i, h + p[i]))
            eset.add(i * n + h + p[i])
    return E


def _haar_start(h, d, rng):
    """Haar graph of Z_h with d random distinct shifts (a cyclic d-regular bipartite start)."""
    S = rng.sample(range(h), d)
    return [(i, h + (i + s) % h) for s in S for i in range(h)]


def _switch_anneal(h, d, D, E, deadline, rng, T0, T1):
    """Anneal edge switches on the d-regular bipartite graph E until diameter <= D.

    Returns (E, cost). cost == 0 means the returned graph has diameter <= D.
    """
    n = 2 * h
    adj = [[] for _ in range(n)]
    eset = set()
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
        eset.add(a * n + b)
    m = len(E)
    cost = _ball_bad(n, adj, D)
    if cost == 0:
        return E, 0

    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    T = T0
    it = 0
    while cost > 0:
        it += 1
        if it % 32 == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = (now - t0) / span
            T = T0 * (T1 / T0) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 * n + b2 in eset or a2 * n + b1 in eset:
            continue
        _swap_apply(E, adj, eset, n, i, a1, b2)
        _swap_apply(E, adj, eset, n, j, a2, b1)
        c2 = _ball_bad(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _swap_apply(E, adj, eset, n, i, a1, b1)
            _swap_apply(E, adj, eset, n, j, a2, b2)
    return E, cost


def _search(d, D, deadline, rng, lo, hi, consider):
    """Bisection on the order N (even) using switch-annealing as the feasibility test."""
    t_begin = time.monotonic()
    total = max(1e-3, deadline - t_begin)
    while True:
        now = time.monotonic()
        if now >= deadline - 0.5:
            break
        N = (lo + hi) // 2
        N -= N % 2
        if N <= lo:
            N = lo + 2
        if N >= hi:
            break
        h = N // 2
        att = min(deadline - now, max(2.0, 0.25 * total))
        if rng.random() < 0.5:
            E = _haar_start(h, d, rng)
        else:
            E = _random_regular(h, d, rng)
        if E is None:
            hi = N
            continue
        E, c = _switch_anneal(h, d, D, E, now + att, rng, 3.0, 0.3)
        if c == 0:
            edges = [(a, b) for a, b in E]
            if lib.is_valid(2 * h, edges, d, D):
                consider(2 * h, edges)
                lo = N
                continue
        hi = N


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

    if D >= 2 and d >= 2:
        moore = lib.moore_bound(d, D)
        lo = max(best_n, 2 * d)
        if lo + 2 < moore:
            _search(d, D, deadline, rng, lo, moore, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
