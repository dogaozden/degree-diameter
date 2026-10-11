import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold alternative family: unstructured search over bipartite d-regular graphs.
#
# Instead of algebraic lifts, we keep a d-regular bipartite graph with h vertices
# per side and minimise the number of vertex pairs farther apart than D, using
# simulated annealing over degree-preserving double-edge switches. The order is
# grown one vertex per side at a time: d edges are subdivided toward a new A
# vertex and a new B vertex (degrees preserved), then annealing repairs the
# diameter. The last valid graph is always kept as the output.
# ----------------------------------------------------------------------------

_T0 = 2.0
_T1 = 0.15


def _cost(nbr, n, D):
    """Ordered count of vertex pairs at distance > D (0 means diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    bad = 0
    for r in reach:
        bad += n - r.bit_count()
    return bad


def _build_nbr(h, E):
    """Adjacency lists for the graph with A = 0..h-1 and B vertices h..2h-1."""
    nbr = [[] for _ in range(2 * h)]
    for a, b in E:
        nbr[a].append(h + b)
        nbr[h + b].append(a)
    return nbr


def _switch(E, i, j, nbr, S, h):
    """Double-edge switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Self-inverse."""
    a1, b1 = E[i]
    a2, b2 = E[j]
    hb1 = h + b1
    hb2 = h + b2
    l = nbr[a1]
    l[l.index(hb1)] = hb2
    l = nbr[a2]
    l[l.index(hb2)] = hb1
    l = nbr[hb1]
    l[l.index(a1)] = a2
    l = nbr[hb2]
    l[l.index(a2)] = a1
    S.discard((a1, b1))
    S.discard((a2, b2))
    S.add((a1, b2))
    S.add((a2, b1))
    E[i] = (a1, b2)
    E[j] = (a2, b1)


def _anneal(h, E, D, deadline, rng):
    """Anneal switches until diameter <= D holds; return edge list (A idx, B idx) or None."""
    E = [tuple(e) for e in E]
    nbr = _build_nbr(h, E)
    S = set(E)
    n = 2 * h
    cost = _cost(nbr, n, D)
    if cost == 0:
        return E
    m = len(E)
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)
    while True:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t_start) / span
        T = _T0 * (_T1 / _T0) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        _switch(E, i, j, nbr, S, h)
        c2 = _cost(nbr, n, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                return list(E)
        else:
            _switch(E, i, j, nbr, S, h)


def _grow(h, E, d, rng):
    """Add one vertex per side: pick d edges with distinct ends, subdivide each toward new A/B vertices."""
    pick = None
    for _ in range(50):
        order = list(range(len(E)))
        rng.shuffle(order)
        used_a, used_b, chosen = set(), set(), []
        for idx in order:
            a, b = E[idx]
            if a in used_a or b in used_b:
                continue
            used_a.add(a)
            used_b.add(b)
            chosen.append(idx)
            if len(chosen) == d:
                break
        if len(chosen) == d:
            pick = chosen
            break
    if pick is None:
        return None
    picked = set(pick)
    newE = [e for k, e in enumerate(E) if k not in picked]
    for idx in pick:
        x, y = E[idx]
        newE.append((x, h))   # x in old A joins new B vertex (index h)
        newE.append((h, y))   # new A vertex (index h) joins old B vertex y
    return newE


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(h, E):
        nonlocal best_n, best_e
        n = 2 * h
        if n > best_n:
            edges = [(a, h + b) for a, b in E]
            if lib.is_valid(n, edges, d, D):
                best_n, best_e = n, edges

    # Known optimal-order graph when d-1 is a prime power and D = 3.
    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        pn, pe = lib.projective_plane_incidence(d - 1)
        if pn > best_n and lib.is_valid(pn, pe, d, D):
            best_n, best_e = pn, pe

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best_n, best_e

    # Starting d-regular bipartite graph: K_{h,h} minus a perfect matching, h = d+1.
    h = d + 1
    E0 = [(i, (i + s) % h) for i in range(h) for s in range(d)]
    cur = _anneal(h, E0, D, total, rng)
    if cur is None:
        return best_n, best_e
    consider(h, cur)
    cur_E = cur

    # Grow one vertex per side at a time; keep the largest valid graph.
    while time.monotonic() < total and 2 * (h + 1) <= moore:
        grown = None
        for _ in range(3):
            now = time.monotonic()
            if now >= total:
                break
            nE = _grow(h, cur_E, d, rng)
            if nE is None:
                continue
            end = min(total, now + max(1.5, 0.5 * (total - now)))
            res = _anneal(h + 1, nE, D, end, rng)
            if res is not None:
                grown = res
                break
        if grown is None:
            break
        h += 1
        cur_E = grown
        consider(h, cur_E)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
