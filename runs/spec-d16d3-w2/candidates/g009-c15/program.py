import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Hub-exempt pencils (new construction, diameter 3).
#
# Start from PG(2,q) incidence. An X-vertex "centred" at point P is joined to
# the q+1 lines through P, except possibly one missing line L. The missing
# line's points are reached through a shared Y-"hub" vertex that is joined to
# all points of L. Symmetrically, a Y-vertex on line j may miss one point P,
# which is covered by an X-hub joined to all lines through P.
#
# Every candidate is checked with lib.is_valid before it is kept, so the
# program never returns an invalid graph; the greedy only adds vertices that
# keep max degree <= d and diameter <= D. The Haar fallback and the
# conic-arc baseline (order 2(q^2+q+1) + 2(q+1)) are always compared too.
# ----------------------------------------------------------------------------


def _largest_pp(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _pg(q):
    """PG(2,q) incidence: points 0..m-1, lines m..2m-1.

    Returns (m, point_lines, line_points, edges) where point_lines[P] lists line
    indices through P and line_points[L] lists point indices on L (both 0-based).
    """
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, pl, lp, list(edges)


def _conic_graph(q, m, pl, lp, edges):
    """Baseline: PG(2,q) plus one X-vertex per conic point and one Y-vertex per conic line.

    The conic (plus nucleus for even q) is an arc, so each line gains at most 2 extra
    neighbours. Valid when d >= q + 3.
    """
    index = {p: i for i, p in enumerate(lib.projective_points(q))}
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        E += [(2 * m + t, m + L) for L in pl[P]]
    for t, j in enumerate(S):
        E += [(Q, 2 * m + k + t) for Q in lp[j]]
    return 2 * m + 2 * k, E


def _grow(d, D, m, pl, lp, edges, rng, deadline):
    """Greedy insertion of hub-exempt pencils into PG(2,q); every step is verified."""
    n = 2 * m
    E = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    fullX = {}  # point index P -> X-vertex joined to all lines through P
    fullY = {}  # line index L  -> Y-vertex joined to all points on L

    def plan(kind, c, miss, n_cur):
        new, reg = [], []
        nxt = n_cur
        if kind == 'X':
            x = nxt
            nxt += 1
            new += [(x, m + L) for L in pl[c] if L != miss]
            if miss is None:
                reg.append(('X', c, x))
            else:
                y = fullY.get(miss)
                if y is None:
                    y = nxt
                    nxt += 1
                    new += [(Q, y) for Q in lp[miss]]
                    reg.append(('Y', miss, y))
                new.append((x, y))
        else:
            y = nxt
            nxt += 1
            new += [(Q, y) for Q in lp[c] if Q != miss]
            if miss is None:
                reg.append(('Y', c, y))
            else:
                x = fullX.get(miss)
                if x is None:
                    x = nxt
                    nxt += 1
                    new += [(x, m + L) for L in pl[miss]]
                    reg.append(('X', miss, x))
                new.append((x, y))
        return new, nxt, reg

    while time.monotonic() < deadline:
        c = rng.randrange(m)
        if rng.random() < 0.5:
            kind = 'X'
            miss = None if rng.random() < 0.4 else rng.choice(pl[c])
        else:
            kind = 'Y'
            miss = None if rng.random() < 0.4 else rng.choice(lp[c])
        new, n2, reg = plan(kind, c, miss, n)
        if not new:
            continue
        cnt = {}
        for u, v in new:
            cnt[u] = cnt.get(u, 0) + 1
            cnt[v] = cnt.get(v, 0) + 1
        if any((deg[w] if w < n else 0) + k > d for w, k in cnt.items()):
            continue
        E2 = E.union((min(u, v), max(u, v)) for u, v in new)
        if len(E2) != len(E) + len(new):
            continue
        if not lib.is_valid(n2, list(E2), d, D):
            continue
        E = E2
        deg.extend([0] * (n2 - n))
        for u, v in new:
            deg[u] += 1
            deg[v] += 1
        n = n2
        for tag, key, vid in reg:
            (fullX if tag == 'X' else fullY).setdefault(key, vid)
    return n, list(E)


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) for D = 4 (diameter 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q); diameter 4, degree q+1."""
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
    """W(q) for the largest prime power q <= min(d-1, 9)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(*gq)

    q = _largest_pp(d - 1)
    if D >= 3 and q is not None:
        m, pl, lp, edges = _pg(q)
        consider(2 * m, edges)
        s = d - q - 1  # spare degree per old vertex
        if s >= 2:
            consider(*_conic_graph(q, m, pl, lp, edges))
        if s >= 1 and time.monotonic() < deadline:
            consider(*_grow(d, D, m, pl, lp, edges, rng, deadline))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
