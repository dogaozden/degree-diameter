import math
import random
import time

import lib


def _moore(d, D):
    """Moore-type ceiling for bipartite graphs with max degree d and diameter D."""
    if D <= 0:
        return 1
    return 2 * sum((d - 1) ** i for i in range(D))


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost(h, D, ea, eb):
    """Number of ordered vertex pairs at distance > D in the bipartite graph
    with sides A = {0..h-1}, B = {h..2h-1} and edges (ea[i], h + eb[i])."""
    n = 2 * h
    adj = [[] for _ in range(n)]
    for a, b in zip(ea, eb):
        adj[a].append(h + b)
        adj[h + b].append(a)
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
    return sum(n - r.bit_count() for r in reach)


def _random_regular(h, d, rng):
    """Random simple d-regular bipartite graph on h + h vertices (union of d perfect matchings)."""
    for _ in range(2000):
        ea, eb, used = [], [], set()
        ok = True
        for _layer in range(d):
            p = list(range(h))
            rng.shuffle(p)
            for a in range(h):
                if (a, p[a]) in used:
                    ok = False
                    break
                used.add((a, p[a]))
                ea.append(a)
                eb.append(p[a])
            if not ok:
                break
        if ok:
            return ea, eb
    return None


def _grow(h, d, ea, eb, rng):
    """Add one A-vertex and one B-vertex, both of degree d, keeping d-regularity.

    Pick d edges forming a matching (a_k, b_k); reroute each to (a_k, b*) and add (a*, b_k).
    Modifies ea, eb in place and returns the new side size, or None if no matching is found.
    """
    E = len(ea)
    idx = list(range(E))
    rng.shuffle(idx)
    chosen, ua, ub = [], set(), set()
    for i in idx:
        if ea[i] not in ua and eb[i] not in ub:
            chosen.append(i)
            ua.add(ea[i])
            ub.add(eb[i])
            if len(chosen) == d:
                break
    if len(chosen) < d:
        return None
    H = h
    for i in chosen:
        b = eb[i]
        eb[i] = H            # edge (a_k, b*)
        ea.append(H)         # edge (a*, b_k)
        eb.append(b)
    return h + 1


def _anneal(h, d, D, ea, eb, rng, deadline, iters):
    """Simulated annealing over edge swaps (degree- and bipartition-preserving).

    Minimises the number of unreached ordered pairs. Returns True iff cost reaches 0.
    """
    E = len(ea)
    eset = set(zip(ea, eb))
    cost = _cost(h, D, ea, eb)
    T0, T1 = 3.0, 0.15
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (t / iters)
        i, j = rng.sample(range(E), 2)
        a1, b1, a2, b2 = ea[i], eb[i], ea[j], eb[j]
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        eset.discard((a1, b1))
        eset.discard((a2, b2))
        eset.add((a1, b2))
        eset.add((a2, b1))
        eb[i], eb[j] = b2, b1
        c2 = _cost(h, D, ea, eb)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            eb[i], eb[j] = b1, b2
            eset.discard((a1, b2))
            eset.discard((a2, b1))
            eset.add((a1, b1))
            eset.add((a2, b2))
    return cost == 0


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 3.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = _moore(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Projective-plane incidence graph (diameter 3) as a structured base.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if best_n >= moore:
        return best

    # Main approach: direct search over bipartite d-regular graphs of growing size.
    # Each stage anneals edge swaps to diameter <= D; on success we grow by two vertices.
    CAP = 700  # cap on total vertices to keep cost evaluations fast
    h = d + 3
    state = _random_regular(h, d, rng)
    if state is not None:
        ea, eb = state
        while time.monotonic() < deadline:
            if _anneal(h, d, D, ea, eb, rng, deadline, 2000):
                if 2 * h > best_n:
                    consider(2 * h, [(a, h + b) for a, b in zip(ea, eb)])
                if best_n >= moore or 2 * (h + 1) > CAP:
                    break
                g = _grow(h, d, ea, eb, rng)
                if g is None:
                    break
                h = g

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
