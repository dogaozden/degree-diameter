import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New approach for D >= 4: simulated annealing over d-regular bipartite graphs
# with a fixed number of vertices per side, using 2-switches (degree-preserving
# edge swaps) to minimise the number of vertex pairs at distance > D.
# When a level reaches zero cost it is recorded, then grown by one vertex per
# side while keeping d-regularity, and annealing continues from the solution.
# D = 3 uses projective planes (Moore-optimal when d-1 is a prime power).
# Every returned candidate is checked with lib.is_valid; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _circulant(h, d):
    """d-regular bipartite graph on h + h vertices: A_i ~ B_{i+s} for s in 0..d-1 (needs h >= d)."""
    E = []
    for i in range(h):
        for s in range(d):
            E.append((i, h + (i + s) % h))
    return E


def _adj_from(n, E):
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    return adj


def _bad(n, adj, D):
    """Number of ordered vertex pairs at distance > D (0 means diameter <= D)."""
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


def _anneal(h, E, D, rng, deadline):
    """Anneal 2-switches on the d-regular graph E (A = 0..h-1, B = h..2h-1, edges stored as (A, B)).

    Returns (cost, E). Cost 0 means the graph has diameter <= D.
    """
    n = 2 * h
    adj = _adj_from(n, E)
    eset = set(E)
    cur = _bad(n, adj, D)
    cycle = 2000
    step = 0
    while cur > 0 and time.monotonic() < deadline:
        frac = (step % cycle) / cycle
        T = 5.0 * (0.04 ** frac)
        step += 1
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        # Apply the 2-switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
        adj[a1].remove(b1)
        adj[b1].remove(a1)
        adj[a2].remove(b2)
        adj[b2].remove(a2)
        adj[a1].append(b2)
        adj[b2].append(a1)
        adj[a2].append(b1)
        adj[b1].append(a2)
        new = _bad(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            eset.discard((a1, b1))
            eset.discard((a2, b2))
            eset.add((a1, b2))
            eset.add((a2, b1))
            E[i] = (a1, b2)
            E[j] = (a2, b1)
            cur = new
        else:
            # Revert.
            adj[a1].remove(b2)
            adj[b2].remove(a1)
            adj[a2].remove(b1)
            adj[b1].remove(a2)
            adj[a1].append(b1)
            adj[b1].append(a1)
            adj[a2].append(b2)
            adj[b2].append(a2)
    return cur, E


def _grow(h, E, d, rng):
    """Go from h to h+1 per side, keeping d-regularity: remove a random d-matching and reconnect to new vertices.

    Old B vertex b (index h..2h-1) is shifted to b+1; new A vertex is h, new B vertex is 2h+1.
    Returns the new edge list, or None if no matching of size d was found.
    """
    E2 = [(a, b + 1) for a, b in E]
    for _ in range(50):
        idx = list(range(len(E2)))
        rng.shuffle(idx)
        usedA = set()
        usedB = set()
        pick = []
        for k in idx:
            a, b = E2[k]
            if a in usedA or b in usedB:
                continue
            usedA.add(a)
            usedB.add(b)
            pick.append(k)
            if len(pick) == d:
                break
        if len(pick) == d:
            break
    else:
        return None
    na = h
    nb = 2 * h + 1
    pickset = set(pick)
    E3 = [e for k, e in enumerate(E2) if k not in pickset]
    for k in pick:
        a, b = E2[k]
        E3.append((na, b))
        E3.append((a, nb))
    return E3


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if best[0] >= moore:
            return best

    rng = random.Random(seed)
    h = d
    E = _circulant(h, d)
    while time.monotonic() < deadline:
        cur, E = _anneal(h, E, D, rng, deadline)
        if cur != 0:
            break
        # Level h is solved: record it, then grow.
        consider(2 * h, list(E))
        if 2 * (h + 1) > moore:
            break
        E2 = _grow(h, E, d, rng)
        if E2 is None:
            h += 1
            E = _circulant(h, d)
        else:
            h += 1
            E = E2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
