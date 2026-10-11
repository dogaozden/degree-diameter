"""Direct simulated-annealing search over d-regular bipartite graphs for D >= 4.

Instead of lifting a base graph, this grows a d-regular bipartite graph one
vertex pair at a time. Each growth step removes a random matching of d edges
and attaches a new left and a new right vertex, which keeps every degree
exactly d. The diameter defect is then reduced by 2-switch moves, which
preserve degrees and bipartiteness, under simulated annealing. Every
accepted state has zero defect, so it is valid for diameter D.

Fallbacks: K_{d,d} always, and PG(2,q) incidence for D >= 3. Every candidate
is checked with lib.is_valid before it is kept.
"""
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


def _bad(nb, V, D):
    """Ordered count of vertex pairs not within distance D (zero means diameter <= D)."""
    reach = [1 << v for v in range(V)]
    for _ in range(D):
        new = [0] * V
        for v in range(V):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return V * V - sum(r.bit_count() for r in reach)


def _replace(lst, old, new):
    lst[lst.index(old)] = new


def _switch(nb, x1, y1, x2, y2):
    """Replace edges (x1,y1),(x2,y2) by (x1,y2),(x2,y1). Left ids are x, right ids are y."""
    _replace(nb[x1], y1, y2)
    _replace(nb[x2], y2, y1)
    _replace(nb[y1], x1, x2)
    _replace(nb[y2], x2, x1)


def _to_nb(L, R, N):
    """Adjacency lists on 2N vertices: left x is x, right y is N + y."""
    nb = [None] * (2 * N)
    for x in range(N):
        nb[x] = [N + y for y in L[x]]
    for y in range(N):
        nb[N + y] = list(R[y])
    return nb


def _to_lr(nb, N):
    L = [[v - N for v in nb[x]] for x in range(N)]
    R = [list(nb[N + y]) for y in range(N)]
    return L, R


def _grow(L, R, N, d, rng):
    """Add one left and one right vertex, keeping d-regularity.

    Remove a matching of d edges (x_i, y_i). Join the new left vertex a to every
    y_i and the new right vertex b to every x_i. Returns (L, R, N+1) or None.
    """
    L = [list(a) for a in L]
    R = [list(b) for b in R]
    order = list(range(N))
    rng.shuffle(order)
    used = set()
    pairs = []
    for x in order:
        opts = [y for y in L[x] if y not in used]
        if not opts:
            continue
        y = rng.choice(opts)
        used.add(y)
        pairs.append((x, y))
        if len(pairs) == d:
            break
    if len(pairs) < d:
        return None
    a = N
    b = N
    L.append([])
    R.append([])
    for x, y in pairs:
        L[x].remove(y)
        R[y].remove(x)
        L[a].append(y)
        R[y].append(a)
        L[x].append(b)
        R[b].append(x)
    return L, R, N + 1


def _anneal(nb, N, d, D, deadline, rng):
    """Anneal 2-switches until the diameter defect is zero. Returns nb on success, else None."""
    V = 2 * N
    cur = _bad(nb, V, D)
    if cur == 0:
        return nb
    T0, Tmin, EPOCH = 2.0, 0.2, 3000
    step = 0
    while True:
        if (step & 31) == 0 and time.monotonic() >= deadline:
            return None
        step += 1
        x1 = rng.randrange(N)
        x2 = rng.randrange(N)
        if x1 == x2:
            continue
        y1 = nb[x1][rng.randrange(d)]
        y2 = nb[x2][rng.randrange(d)]
        if y2 in nb[x1] or y1 in nb[x2]:
            continue
        _switch(nb, x1, y1, x2, y2)
        c = _bad(nb, V, D)
        if c == 0:
            return nb
        delta = c - cur
        j = step % EPOCH
        T = T0 * (Tmin / T0) ** (j / EPOCH)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c
        else:
            _switch(nb, x1, y2, x2, y1)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    deadline = start + 0.8 * time_limit

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

    if D >= 4 and d >= 1:
        # Start from K_{d,d} and grow by warm-started annealing.
        L = [list(range(d)) for _ in range(d)]
        R = [list(range(d)) for _ in range(d)]
        N = d
        while time.monotonic() < deadline:
            g = _grow(L, R, N, d, rng)
            if g is None:
                break
            L2, R2, N2 = g
            nb = _to_nb(L2, R2, N2)
            remaining = deadline - time.monotonic()
            budget = remaining if remaining < 3.0 else max(3.0, 0.3 * remaining)
            res = _anneal(nb, N2, d, D, time.monotonic() + budget, rng)
            if res is not None:
                edges = [(x, v) for x in range(N2) for v in res[x]]
                if 2 * N2 > best_n and lib.is_valid(2 * N2, edges, d, D):
                    best = (2 * N2, edges)
                    best_n = 2 * N2
                L, R = _to_lr(res, N2)
                N = N2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
