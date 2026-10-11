import math
import random
import time

import lib


def _cost(h, An, Bn, D):
    """Number of ordered (source, target) pairs at distance > D in the bipartite graph.

    A-vertices are ids 0..h-1, B-vertices are ids h..2h-1 (B id j maps to vertex h+j).
    Zero means the graph has diameter <= D.
    """
    n = 2 * h
    adj = [None] * n
    for i in range(h):
        adj[i] = [h + j for j in An[i]]
    for j in range(h):
        adj[h + j] = Bn[j]
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal(h, An, Bn, d, D, deadline, rng):
    """Edge-switch simulated annealing on a d-regular bipartite graph.

    A switch replaces edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). This keeps the
    graph bipartite and d-regular. Returns the final cost (0 means success).
    """
    cost = _cost(h, An, Bn, D)
    if cost == 0:
        return 0
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 3.0, 0.2
    T = T0
    it = 0
    while cost > 0:
        it += 1
        if (it & 7) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = min(1.0, (now - t0) / span)
            T = T0 * (T1 / T0) ** frac
        i1 = rng.randrange(h)
        k1 = rng.randrange(d)
        i2 = rng.randrange(h)
        k2 = rng.randrange(d)
        if i1 == i2:
            continue
        j1 = An[i1][k1]
        j2 = An[i2][k2]
        if j1 == j2 or j2 in An[i1] or j1 in An[i2]:
            continue
        p1 = Bn[j1].index(i1)
        p2 = Bn[j2].index(i2)
        An[i1][k1] = j2
        An[i2][k2] = j1
        Bn[j1][p1] = i2
        Bn[j2][p2] = i1
        c2 = _cost(h, An, Bn, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            An[i1][k1] = j1
            An[i2][k2] = j2
            Bn[j1][p1] = i1
            Bn[j2][p2] = i2
    return cost


def _grow(h, An, Bn, d, rng):
    """Insert one new A-vertex and one new B-vertex, keeping d-regularity.

    Pick d edges (a_i, b_j) with distinct endpoints. Re-route each one: a_i now
    goes to the new B-vertex b*, and b_j now goes to the new A-vertex a*.
    Returns True on success (the caller must then increase h by 1).
    """
    picks = None
    for _ in range(300):
        rows = rng.sample(range(h), d)
        cand = []
        used = set()
        ok = True
        for i in rows:
            k = rng.randrange(d)
            j = An[i][k]
            if j in used:
                ok = False
                break
            used.add(j)
            cand.append((i, k, j))
        if ok:
            picks = cand
            break
    if picks is None:
        return False
    new_a = h
    new_b = h
    newA = []
    newB = []
    for i, k, j in picks:
        p = Bn[j].index(i)
        An[i][k] = new_b
        Bn[j][p] = new_a
        newA.append(j)
        newB.append(i)
    An.append(newA)
    Bn.append(newB)
    return True


def _edges(h, An):
    return [(i, h + j) for i in range(h) for j in An[i]]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # A cycle of length 2D is bipartite, 2-regular, and has diameter D (optimal).
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        # Projective plane incidence graphs are optimal for D = 3 (Moore bound).
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                if q == d - 1:
                    return best
                break

    # Unstructured search: grow a d-regular bipartite graph by insertion,
    # and after each insertion repair the diameter by edge-switch annealing.
    h = d
    An = [list(range(d)) for _ in range(d)]
    Bn = [list(range(d)) for _ in range(d)]
    while time.monotonic() < deadline:
        cost = _anneal(h, An, Bn, d, D, deadline, rng)
        if cost != 0:
            break
        consider(2 * h, _edges(h, An))
        if not _grow(h, An, Bn, d, rng):
            break
        h += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
