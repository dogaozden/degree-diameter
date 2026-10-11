"""Conic-extended projective plane graphs, with a greedy vertex-growth pass.

Base: incidence graph of PG(2, q), q the largest prime power with q + 1 <= d.
Spare degree s = d - q - 1 on every vertex is used by adding
  * a point-side vertex A_P for each point P in a set X, joined to the q+1 lines through P,
  * a line-side vertex B_L for each line L in a set Y, joined to the q+1 points on L.
X must put at most s points on every line, and Y at most s lines through every point.
Every such choice keeps diameter 3 and bipartiteness.

For odd q and s >= 2, X is a conic (q+1 points, no three collinear) and Y is its set of
tangent lines. Both are 2-arcs, so this gives 2(q^2+q+1) + 2(q+1) vertices. For d = 16 this
is 394, which matches the record. It cannot go higher inside this family, because the
multiset argument shows that |X| <= q+1 whenever every line holds at most two of its points.
The growth pass then tries to attach extra vertices whose neighbourhoods cover all
vertices within distance 2, and keeps only what lib.is_valid accepts.
"""
import random
import time

import lib


def _largest_pp(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _pg(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q). Points 0..m-1, lines m..2m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _loads_ok(items, tgt, m, s):
    """True if every target index is hit by at most s of the chosen items."""
    load = [0] * m
    for i in items:
        for t in tgt[i]:
            load[t] += 1
    return max(load, default=0) <= s


def _pack(tgt, m, s, order):
    """Greedy: take items in the given order while every target keeps load <= s."""
    load = [0] * m
    chosen = []
    for i in order:
        T = tgt[i]
        if all(load[t] < s for t in T):
            chosen.append(i)
            for t in T:
                load[t] += 1
    return chosen


def _best_arcs(q, m, s, pl, lp, rng, deadline):
    """Return (X, Y): X a set of points, Y a set of lines, each with load <= s on the other side."""
    bestX, bestY = [], []
    if q % 2 == 1 and s >= 2:
        F = lib.GF(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        conic = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
        if _loads_ok(conic, pl, m, s):
            bestX = conic
            cnt = [0] * m
            for P in conic:
                for L in pl[P]:
                    cnt[L] += 1
            tang = [L for L in range(m) if cnt[L] == 1]
            if _loads_ok(tang, lp, m, s) and len(tang) > len(bestY):
                bestY = tang
    order = list(range(m))
    for _ in range(3000):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        X = _pack(pl, m, s, order)
        if len(X) > len(bestX):
            bestX = X
        Y = _pack(lp, m, s, order)
        if len(Y) > len(bestY):
            bestY = Y
    return bestX, bestY


def _cover(cands, ball2, full, d):
    """Greedy cover of `full` by at most d candidate neighbourhoods; None on failure."""
    covered = 0
    chosen = []
    pool = list(cands)
    while covered != full:
        if len(chosen) >= d or not pool:
            return None
        bi, bg = -1, 0
        for idx, u in enumerate(pool):
            g = (ball2[u] & ~covered).bit_count()
            if g > bg:
                bg, bi = g, idx
        if bi < 0:
            return None
        u = pool.pop(bi)
        chosen.append(u)
        covered |= ball2[u]
    return chosen


def _grow(n, edges, col, d, deadline):
    """Repeatedly add a vertex whose neighbours (opposite colour, spare degree) cover everything within 2.

    Such a vertex is within distance 3 of all old vertices, and old distances only shrink,
    so the diameter bound is preserved by construction.
    """
    edges = list(edges)
    while time.monotonic() < deadline:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        ball1 = []
        for u in range(n):
            b = 1 << u
            for v in adj[u]:
                b |= 1 << v
            ball1.append(b)
        ball2 = []
        for u in range(n):
            b = ball1[u]
            for v in adj[u]:
                b |= ball1[v]
            ball2.append(b)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [u for u in range(n) if col[u] == 1 - c and len(adj[u]) < d]
            chosen = _cover(cands, ball2, full, d)
            if chosen:
                v = n
                n += 1
                col.append(c)
                for u in chosen:
                    edges.append((u, v))
                added = True
                break
        if not added:
            break
    return n, edges


def _pg_extension(q, d, arc_deadline, grow_deadline, rng):
    """PG(2,q) incidence plus A/B arc extensions, then cover-based growth."""
    m, edges, pl, lp = _pg(q)
    s = d - q - 1
    if s <= 0:
        return 2 * m, list(edges)
    X, Y = _best_arcs(q, m, s, pl, lp, rng, arc_deadline)
    E = list(edges)
    n = 2 * m
    col = [0] * m + [1] * m
    for P in X:
        x = n
        n += 1
        col.append(0)
        for L in pl[P]:
            E.append((x, m + L))
    for L in Y:
        b = n
        n += 1
        col.append(1)
        for Q in lp[L]:
            E.append((Q, b))
    return _grow(n, E, col, d, grow_deadline)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        q = _largest_pp(d - 1)
        if q is not None:
            try:
                n, E = _pg_extension(q, d,
                                     start + 0.3 * time_limit,
                                     start + 0.8 * time_limit,
                                     rng)
                if n > best[0] and lib.is_valid(n, E, d, D):
                    best = (n, E)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
