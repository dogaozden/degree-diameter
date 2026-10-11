import math
import random
import time

import lib


def _nbrs(s, E):
    """Adjacency lists for a bipartite graph: left vertices 0..s-1, right vertices s..2s-1."""
    nbr = [[] for _ in range(2 * s)]
    for a, b in E:
        nbr[a].append(s + b)
        nbr[s + b].append(a)
    return nbr


def _bad_pairs(n, nbr, D):
    """Number of unordered vertex pairs at distance more than D (bitmask BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        changed = False
        for v in range(n):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            if r != reach[v]:
                changed = True
            new.append(r)
        reach = new
        if not changed:
            break
    return sum(n - r.bit_count() for r in reach) // 2


def _extend(s, E, d, rng):
    """Edge-splitting growth: add one left vertex x and one right vertex y, both of degree d.

    Each step removes an edge (a, b) and adds (x, b) and (a, y). Degrees of old
    vertices are preserved, the graph stays simple and bipartite, and x and y reach degree d.
    Returns (s + 1, new_E), or None if the splitting fails.
    """
    E = [list(e) for e in E]
    x, y = s, s
    NX, NY = set(), set()
    for _ in range(d):
        placed = False
        for _try in range(400):
            i = rng.randrange(len(E))
            a, b = E[i]
            if a < s and b < s and a not in NY and b not in NX:
                E[i] = [x, b]
                E.append([a, y])
                NX.add(b)
                NY.add(a)
                placed = True
                break
        if not placed:
            return None
    return s + 1, E


def _anneal(s, d, D, E, deadline, T0, T1, rng):
    """Simulated annealing over 2-switches of a d-regular bipartite graph.

    A 2-switch takes edges (a, b), (c, e) to (a, e), (c, b). It keeps every degree
    and the bipartition. The cost is the number of bad pairs (distance > D).
    Returns the edge list when cost 0 is reached, else None.
    """
    E = [list(e) for e in E]
    n = 2 * s
    m = len(E)
    present = {a * s + b for a, b in E}
    cost = _bad_pairs(n, _nbrs(s, E), D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        if a * s + e in present or c * s + b in present:
            continue
        E[i] = [a, e]
        E[j] = [c, b]
        new = _bad_pairs(n, _nbrs(s, E), D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
            present.discard(a * s + b)
            present.discard(c * s + e)
            present.add(a * s + e)
            present.add(c * s + b)
        else:
            E[i] = [a, b]
            E[j] = [c, e]
    return E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)

    # Fallback: K_{d,d} has diameter 2 and degree d.
    s = d
    E = [[a, b] for a in range(d) for b in range(d)]
    best = (2 * d, [(a, d + b) for a, b in E])
    best_n = 2 * d

    # Ladder: grow the graph one vertex per side by edge splitting, then repair
    # the diameter by annealing 2-switches. On failure, retry from the last success.
    fails = 0
    budget = 1.5
    while time.monotonic() < deadline:
        ext = _extend(s, E, d, rng)
        if ext is None:
            break
        s2, E2 = ext
        stage_end = min(deadline, time.monotonic() + budget)
        res = _anneal(s2, d, D, E2, stage_end, 1.5, 0.15, rng)
        if res is not None:
            s, E = s2, res
            fails = 0
            budget = 1.5
            if 2 * s > best_n:
                cand_n = 2 * s
                cand_e = [(a, s + b) for a, b in E]
                if lib.is_valid(cand_n, cand_e, d, D):
                    best = (cand_n, cand_e)
                    best_n = cand_n
        else:
            fails += 1
            budget = min(10.0, 1.5 * (1.25 ** fails))

    if not lib.is_valid(best[0], best[1], d, D):
        best = (2 * d, [(a, d + b) for a in range(d) for b in range(d)])
    return best
