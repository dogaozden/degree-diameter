import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (kept as fallbacks).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: grow-and-repair on bipartite d-regular graphs.
#
# Start from K_{d,d} (diameter 2). Repeatedly:
#   * if the current graph has diameter <= D, record it and grow it by adding one
#     A-vertex and one B-vertex. Growth picks d disjoint edges (a_i, b_i), replaces
#     each by (a_i, b') and adds (a', b_i). Every old degree is kept, so the graph
#     stays d-regular and bipartite.
#   * otherwise repair it with simulated annealing over degree-preserving
#     double-edge swaps, minimising the number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of ordered vertex pairs at distance > D (zero iff diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nr = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nr.append(r)
        reach = nr
    return sum(n - r.bit_count() for r in reach)


def _grow_repair(d, D, rng, deadline, record):
    n = 2 * d
    adj = [set() for _ in range(n)]
    E = []
    Eset = set()
    for a in range(d):
        for b in range(d, 2 * d):
            E.append((a, b))
            Eset.add((a, b))
            adj[a].add(b)
            adj[b].add(a)

    def replace(idx, na, nb):
        oa, ob = E[idx]
        Eset.discard((oa, ob))
        adj[oa].discard(ob)
        adj[ob].discard(oa)
        E[idx] = (na, nb)
        Eset.add((na, nb))
        adj[na].add(nb)
        adj[nb].add(na)

    def add_edge(a, b):
        E.append((a, b))
        Eset.add((a, b))
        adj[a].add(b)
        adj[b].add(a)

    def extend():
        nonlocal n
        order = list(range(len(E)))
        rng.shuffle(order)
        ua, ub, chosen = set(), set(), []
        for idx in order:
            a, b = E[idx]
            if a in ua or b in ub:
                continue
            ua.add(a)
            ub.add(b)
            chosen.append(idx)
            if len(chosen) == d:
                break
        if len(chosen) < d:
            return False
        na, nb = n, n + 1
        n += 2
        adj.append(set())
        adj.append(set())
        bs = []
        for idx in chosen:
            a, b = E[idx]
            bs.append(b)
            replace(idx, a, nb)
        for b in bs:
            add_edge(na, b)
        return True

    c = _bad(n, adj, D)
    T = 0.6
    while time.monotonic() < deadline:
        if c == 0:
            record(n, list(E))
            if not extend():
                break
            c = _bad(n, adj, D)
            continue
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in Eset or (a2, b1) in Eset:
            continue
        replace(i, a1, b2)
        replace(j, a2, b1)
        c2 = _bad(n, adj, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            replace(j, a2, b2)
            replace(i, a1, b1)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, list(e))
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: grow-and-repair on d-regular bipartite graphs.
    if d >= 3 and D >= 2 and time.monotonic() < deadline:
        try:
            _grow_repair(d, D, rng, deadline, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
