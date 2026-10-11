import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4, (q+1)-regular).
# Used as a regular seed for D >= 4 when d - 1 is a small prime power.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q). Points are 0..P-1, lines P..2P-1."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Unstructured d-regular bipartite search with incremental growth.
#
# State: k vertices per side. Side-0 vertex x is id x, side-1 vertex y is id k+y.
# E is a list of (x, y) pairs; eset is the same set for O(1) membership.
# Every vertex has degree exactly d, so the graph is bipartite by construction.
#
# Growth: remove d-1 disjoint edges, add one vertex to each side, and join them
# to the freed endpoints plus each other. Degrees stay d. Then anneal with
# degree-preserving 2-switches, minimizing the number of vertex pairs at
# distance > D.
# ----------------------------------------------------------------------------

def _adj_of(k, E):
    adj = [[] for _ in range(2 * k)]
    for x, y in E:
        adj[x].append(k + y)
        adj[k + y].append(x)
    return adj


def _bad_pairs_adj(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitset BFS)."""
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
    return sum(n - r.bit_count() for r in reach) // 2


def _extend(k, E, d, rng):
    """Add one vertex per side to a d-regular state, keeping all degrees at d."""
    order = list(range(len(E)))
    rng.shuffle(order)
    usedx, usedy, chosen = set(), set(), []
    for i in order:
        x, y = E[i]
        if x in usedx or y in usedy:
            continue
        usedx.add(x)
        usedy.add(y)
        chosen.append(i)
        if len(chosen) == d - 1:
            break
    if len(chosen) < d - 1:
        return None, None
    a = k
    b = k
    chosen_set = set(chosen)
    newE = [E[i] for i in range(len(E)) if i not in chosen_set]
    for i in chosen:
        x, y = E[i]
        newE.append((a, y))
        newE.append((x, b))
    newE.append((a, b))
    return k + 1, newE


def _anneal(k, E, eset, D, rng, deadline, max_iters):
    """2-switch annealing on E (modified in place). Returns final cost; 0 means valid."""
    n = 2 * k
    cost = _bad_pairs_adj(n, _adj_of(k, E), D)
    T = 0.6
    m = len(E)
    for it in range(max_iters):
        if cost == 0:
            return 0
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        x1, y1 = E[i]
        x2, y2 = E[j]
        if x1 == x2 or y1 == y2:
            continue
        if (x1, y2) in eset or (x2, y1) in eset:
            continue
        E[i] = (x1, y2)
        E[j] = (x2, y1)
        eset.discard((x1, y1))
        eset.discard((x2, y2))
        eset.add((x1, y2))
        eset.add((x2, y1))
        c2 = _bad_pairs_adj(n, _adj_of(k, E), D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            E[i] = (x1, y1)
            E[j] = (x2, y2)
            eset.discard((x1, y2))
            eset.discard((x2, y1))
            eset.add((x1, y1))
            eset.add((x2, y2))
    return cost


def _state_from_graph(n, edges, d):
    """Convert a d-regular bipartite graph with sides 0..n/2-1 and n/2..n-1 into (k, E)."""
    k = n // 2
    deg = [0] * n
    E = []
    for u, v in edges:
        if u > v:
            u, v = v, u
        if not (u < k <= v):
            return None
        E.append((u, v - k))
        deg[u] += 1
        deg[v] += 1
    if any(x != d for x in deg):
        return None
    if len(set(E)) != len(E):
        return None
    return k, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed * 1000003 + d * 101 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Exact Moore-bound construction when d-1 is a prime power and D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if d == 2:
        # Even cycle of length 2D: bipartite, degree 2, diameter D.
        if D >= 2:
            n = 2 * D
            cyc = [(i, (i + 1) % n) for i in range(n)]
            if lib.is_valid(n, cyc, d, D) and n > best[0]:
                best = (n, cyc)
        return best

    if d < 3 or D < 2:
        return best

    def record(k, E):
        nonlocal best
        n = 2 * k
        if n > best[0]:
            edges = [(x, k + y) for x, y in E]
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)

    # Initial regular seed.
    k = d
    E = [(x, y) for x in range(d) for y in range(d)]
    if D >= 4 and 2 <= d - 1 <= 5 and lib.is_prime_power(d - 1):
        try:
            gn, ge = _gq_w(d - 1)
            st = _state_from_graph(gn, ge, d)
            if st is not None and lib.is_valid(gn, ge, d, D):
                k, E = st
        except Exception:
            k = d
            E = [(x, y) for x in range(d) for y in range(d)]

    eset = set(E)
    record(k, E)

    # Incremental growth with annealing at each size.
    fails = 0
    while time.monotonic() < deadline and fails < 3:
        k2, E2 = _extend(k, E, d, rng)
        if E2 is None:
            break
        eset2 = set(E2)
        max_iters = 300 + 15 * 2 * k2
        cost = _anneal(k2, E2, eset2, D, rng, deadline, max_iters)
        if cost == 0:
            k, E, eset = k2, E2, eset2
            record(k, E)
            fails = 0
        else:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
