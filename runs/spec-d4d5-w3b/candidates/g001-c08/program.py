import math
import random
import time

import lib


def _bad_pairs(N, E, D):
    """Number of unordered vertex pairs at distance > D in the bipartite graph.

    A-vertices are 0..N-1, B-vertices are N..2N-1; E holds (a, b) with b a B-index.
    """
    n = 2 * N
    nbr = [[] for _ in range(n)]
    for a, b in E:
        nbr[a].append(N + b)
        nbr[N + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal(N, D, E0, rng, deadline, steps, T_hi=1.5, T_lo=0.15):
    """Edge-switch annealing on a d-regular bipartite graph, minimising bad pairs.

    A switch replaces (a1,b1),(a2,b2) by (a1,b2),(a2,b1); degrees are preserved.
    Returns (best_cost, best_edge_list).
    """
    E = list(E0)
    eset = set(E)
    cost = _bad_pairs(N, E, D)
    best_cost, best_E = cost, list(E)
    m = len(E)
    for step in range(steps):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T_hi * (T_lo / T_hi) ** (step / steps)
        i, j = rng.sample(range(m), 2)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        eset.discard((a1, b1))
        eset.discard((a2, b2))
        eset.add((a1, b2))
        eset.add((a2, b1))
        c2 = _bad_pairs(N, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost < best_cost:
                best_cost, best_E = cost, list(E)
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            eset.discard((a1, b2))
            eset.discard((a2, b1))
            eset.add((a1, b1))
            eset.add((a2, b2))
    return best_cost, best_E


def _grow(N, E, d, rng):
    """Add one vertex to each side: remove a d-edge matching and join the new vertices to it.

    Degrees stay exactly d. Returns (N+1, new_edges) or None if no matching was found.
    """
    chosen = None
    for _ in range(200):
        idx = list(range(len(E)))
        rng.shuffle(idx)
        usedA, usedB, pick = set(), set(), []
        for k in idx:
            a, b = E[k]
            if a in usedA or b in usedB:
                continue
            usedA.add(a)
            usedB.add(b)
            pick.append(k)
            if len(pick) == d:
                break
        if len(pick) == d:
            chosen = pick
            break
    if chosen is None:
        return None
    ch = set(chosen)
    newE = [e for k, e in enumerate(E) if k not in ch]
    for k in chosen:
        a, b = E[k]
        newE.append((N, b))   # new A-vertex N joins the old B-endpoint
        newE.append((a, N))   # new B-vertex N joins the old A-endpoint
    return N + 1, newE


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    # Exact Moore-bound family: projective plane incidence graph when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Warm-started growth search over d-regular bipartite graphs with N vertices per side.
    # Each size is attempted from the last solved graph; annealing minimises bad pairs.
    best_N = d
    best_E = [(a, b) for a in range(d) for b in range(d)]
    while time.monotonic() < deadline:
        g = _grow(best_N, best_E, d, rng)
        if g is None:
            break
        N2, E2 = g
        solved = False
        while time.monotonic() < deadline:
            c, bE = _anneal(N2, D, E2, rng, deadline, steps=3000)
            if c == 0:
                best_N, best_E = N2, bE
                solved = True
                break
            E2 = bE
        if not solved:
            break

    n = 2 * best_N
    edges = [(a, best_N + b) for a, b in best_E]
    if best_N > d and lib.is_valid(n, edges, d, D):
        return n, edges
    return fallback
