"""Grow-and-anneal construction: add two vertices (one per side) to a valid
bipartite graph, re-wire them in with degree-preserving moves, then anneal
double-edge swaps until the diameter bound holds again. Repeat while it succeeds."""
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


def _bip_colors(n, nb):
    """Proper 2-colouring of a bipartite graph given by neighbour sets."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in nb[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _set_edge(nb, a, b, on):
    if on:
        nb[a].add(b)
        nb[b].add(a)
    else:
        nb[a].discard(b)
        nb[b].discard(a)


def _bad_pairs(n, nb, D):
    """Number of unordered pairs at distance greater than D (bitset BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _attach(me, nbr_side, excl, n, col, nb, d, rng, deficient):
    """Give vertex `me` up to degree d by joining it to vertices on nbr_side.

    If no free vertex is left, steal an edge (a, v) from a full vertex v and
    record a as deficient, to be repaired by the fill step."""
    cand = [v for v in range(n)
            if col[v] == nbr_side and v not in excl and len(nb[v]) < d]
    rng.shuffle(cand)
    for v in cand:
        if len(nb[me]) >= d:
            break
        _set_edge(nb, me, v, True)
    while len(nb[me]) < d:
        full = [v for v in range(n)
                if col[v] == nbr_side and v not in excl
                and len(nb[v]) >= d and v not in nb[me]]
        if not full:
            break
        v = rng.choice(full)
        opts = [a for a in nb[v] if a != me]
        if not opts:
            break
        a = rng.choice(opts)
        _set_edge(nb, a, v, False)
        deficient.append(a)
        _set_edge(nb, me, v, True)


def _fill(n, col, nb, d, rng):
    """Greedily join deficient vertices across the bipartition."""
    A = [v for v in range(n) if col[v] == 0 and len(nb[v]) < d]
    B = [v for v in range(n) if col[v] == 1 and len(nb[v]) < d]
    rng.shuffle(B)
    for a in A:
        for b in B:
            if len(nb[a]) >= d:
                break
            if len(nb[b]) < d and b not in nb[a]:
                _set_edge(nb, a, b, True)


def _grow_pair(n, col, nb, d, rng):
    """Append one vertex per side, wire them in, and fill deficiencies. Returns new n."""
    x, y = n, n + 1
    col.extend([0, 1])
    nb.append(set())
    nb.append(set())
    excl = {x, y}
    deficient = []
    _attach(x, 1, excl, n + 2, col, nb, d, rng, deficient)
    _attach(y, 0, excl, n + 2, col, nb, d, rng, deficient)
    _fill(n + 2, col, nb, d, rng)
    return n + 2


def _anneal(n, col, nb, d, D, rng, deadline, iters):
    """Metropolis search over degree-preserving double-edge swaps minimising bad pairs."""
    E = [(u, v) for u in range(n) if col[u] == 0 for v in nb[u]]
    if not E:
        return False
    cost = _bad_pairs(n, nb, D)
    T = 1.0
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = max(0.2, T * 0.998)
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if b2 in nb[a1] or b1 in nb[a2]:
            continue
        _set_edge(nb, a1, b1, False)
        _set_edge(nb, a2, b2, False)
        _set_edge(nb, a1, b2, True)
        _set_edge(nb, a2, b1, True)
        c2 = _bad_pairs(n, nb, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            E[i] = (a1, b2)
            E[j] = (a2, b1)
        else:
            _set_edge(nb, a1, b2, False)
            _set_edge(nb, a2, b1, False)
            _set_edge(nb, a1, b1, True)
            _set_edge(nb, a2, b2, True)
    return cost == 0


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Base: K_{d,d} (diameter 2), or PG(2,q) incidence when D >= 3 and it is larger.
    best = lib.haar_graph(d, range(d))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

    n, edges = best
    nb = [set() for _ in range(n)]
    for u, v in edges:
        nb[u].add(v)
        nb[v].add(u)
    col = _bip_colors(n, nb)

    moore = lib.moore_bound(d, D)
    iters = 1500 if D >= 5 else 600
    fails = 0
    while time.monotonic() < deadline and fails < 20 and n + 2 <= moore:
        nb2 = [set(s) for s in nb]
        col2 = list(col)
        n2 = _grow_pair(n, col2, nb2, d, rng)
        if _anneal(n2, col2, nb2, d, D, rng, deadline, iters):
            n, nb, col = n2, nb2, col2
            fails = 0
        else:
            fails += 1

    if n > best[0]:
        out = sorted((u, v) for u in range(n) for v in nb[u] if u < v)
        if lib.is_valid(n, out, d, D):
            return n, out
    return best
