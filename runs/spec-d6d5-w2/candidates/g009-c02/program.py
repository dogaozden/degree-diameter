import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family: random d-regular bipartite graphs optimised by edge switches.
#
# Vertices A = 0..N-1 and B = N..2N-1. Every edge joins A to B. A switch
# replaces (a1,b1),(a2,b2) by (a1,b2),(a2,b1), which keeps all degrees fixed.
# The cost is the number of ordered pairs at distance > D, computed with
# bitmask ball expansion. Zero cost means diameter <= D.
# ----------------------------------------------------------------------------

def _balls(n, adj, D):
    """Bitmask per vertex of all vertices within distance D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return reach


def _bad(n, adj, D):
    """Number of ordered vertex pairs at distance more than D (unreachable counts)."""
    return sum(n - r.bit_count() for r in _balls(n, adj, D))


def _rewire(adj, a1, b1, a2, b2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1) in adjacency lists."""
    adj[a1].remove(b1)
    adj[a1].append(b2)
    adj[b1].remove(a1)
    adj[b1].append(a2)
    adj[a2].remove(b2)
    adj[a2].append(b1)
    adj[b2].remove(a2)
    adj[b2].append(a1)


def _anneal(N, d, D, rng, deadline):
    """Anneal a random bipartite graph with sides of size N. Returns edge list or None."""
    n = 2 * N
    es = set()
    for _ in range(d):
        p = list(range(N))
        rng.shuffle(p)
        for a in range(N):
            es.add((a, N + p[a]))
    el = list(es)
    adj = [[] for _ in range(n)]
    for a, b in el:
        adj[a].append(b)
        adj[b].append(a)
    cost = _bad(n, adj, D)
    m = len(el)
    if m < 2:
        return None

    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while True:
        if cost == 0:
            return el
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        T = 3.0 * (0.05 / 3.0) ** frac

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = el[i]
        a2, b2 = el[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in es or (a2, b1) in es:
            continue

        _rewire(adj, a1, b1, a2, b2)
        c2 = _bad(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            es.discard((a1, b1))
            es.discard((a2, b2))
            es.add((a1, b2))
            es.add((a2, b1))
            el[i] = (a1, b2)
            el[j] = (a2, b1)
        else:
            _rewire(adj, a1, b2, a2, b1)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D <= 3:
        return best

    # Main search for D >= 4: random bipartite regular graphs with edge switches.
    # Start from a size that is already known to be reachable, climb on success,
    # and step down on failure.
    N = max(d + 1, best[0] // 2 + 2)
    while time.monotonic() < deadline - 0.5:
        remaining = deadline - time.monotonic()
        budget = max(2.0, 0.3 * remaining)
        budget = min(budget, remaining)
        el = _anneal(N, d, D, rng, time.monotonic() + budget)
        if el is not None:
            consider(2 * N, el)
            N += 2
        else:
            N = max(d + 1, N - 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
