import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has spare degree
# s = d - q - 1. An arc S of points (each line holds <= s points of S, each
# point lies on <= s lines of S) gets one new A-vertex per point (joined to the
# lines through it) and one new B-vertex per point (joined to the points on it).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, S, point_lines, line_points):
    """Vertices: points 0..m-1, lines m..2m-1, A-vertices 2m.., B-vertices after them."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


# ----------------------------------------------------------------------------
# Monotone growth with a cover certificate (diameter 3, bipartite).
#
# Adding edges or vertices never lengthens an existing shortest path, so a valid
# graph stays valid while we grow it. A new vertex x on side t is at distance
# <= 3 from everything if its neighbourhood N (all on the opposite side, with
# spare degree) satisfies: every existing side-t vertex has a neighbour in N.
# Vertices on the opposite side are then at distance 1 or 3. We find such N by
# greedy set cover, then check the result with lib.is_valid anyway.
# ----------------------------------------------------------------------------

def _cover(same, cand, adj, d, rng, tries=3):
    """Choose <= d vertices from cand whose neighbourhoods cover all of same; None if it fails."""
    for _ in range(tries):
        rng.shuffle(cand)
        uncovered = set(same)
        chosen = []
        used = set()
        while uncovered and len(chosen) < d:
            best_v, best_g = -1, 0
            for v in cand:
                if v in used:
                    continue
                g = len(adj[v] & uncovered)
                if g > best_g:
                    best_g, best_v = g, v
            if best_v < 0:
                break
            chosen.append(best_v)
            used.add(best_v)
            uncovered -= adj[best_v]
        if not uncovered and chosen:
            return chosen
    return None


def _densify(adj, side, d, rng, tries):
    """Add random edges between spare-degree vertices on opposite sides (only shortens paths)."""
    n = len(side)
    for _ in range(tries):
        u = rng.randrange(n)
        v = rng.randrange(n)
        if side[u] == side[v] or v in adj[u]:
            continue
        if len(adj[u]) >= d or len(adj[v]) >= d:
            continue
        adj[u].add(v)
        adj[v].add(u)


def _grow(n, E, side0, d, D, deadline, rng):
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    side = list(side0)
    best_n, best_E = n, list(E)
    fails = 0
    while time.monotonic() < deadline and fails < 40:
        t = rng.randrange(2)
        N_ = len(side)
        same = [v for v in range(N_) if side[v] == t]
        cand = [v for v in range(N_) if side[v] != t and len(adj[v]) < d]
        chosen = _cover(same, cand, adj, d, rng)
        if chosen is None:
            fails += 1
            continue
        x = N_
        side.append(t)
        adj.append(set())
        for v in chosen:
            adj[x].add(v)
            adj[v].add(x)
        if rng.random() < 0.5:
            _densify(adj, side, d, rng, 40)
        E2 = [(u, v) for u in range(len(side)) for v in adj[u] if u < v]
        if not lib.is_valid(len(side), E2, d, D):
            break
        best_n, best_E = len(side), E2
        fails = 0
    return best_n, best_E


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) baseline (D >= 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        starts = []
        for q in range(2, min(d - 1, 23) + 1):
            if not lib.is_prime_power(q):
                continue
            s = d - q - 1
            if s < 0:
                continue
            m, edges, pl, lp, index = _pg_data(q)
            cands = [[]]
            if s >= 1:
                cands.append(_greedy_arc(m, s, pl, lp, rng, 30, start + 0.15 * time_limit))
            if s >= 2:
                cs = _conic_set(q, index, lib.GF(q))
                if _loads_ok(cs, s, m, pl, lp):
                    cands.append(cs)
            S = max(cands, key=len)
            if not _loads_ok(S, s, m, pl, lp):
                continue
            n_c, e_c = _arc_graph(m, edges, S, pl, lp)
            side = [0] * m + [1] * m + [0] * len(S) + [1] * len(S)
            starts.append((n_c, e_c, side))
            consider(n_c, e_c)

        # Grow each of the largest starts by monotone cover-certified addition.
        starts.sort(key=lambda t: -t[0])
        starts = starts[:3]
        for idx, (n_c, e_c, side_c) in enumerate(starts):
            now = time.monotonic()
            if now >= deadline:
                break
            share = (deadline - now) / (len(starts) - idx)
            gn, ge = _grow(n_c, e_c, side_c, d, D, now + share,
                           random.Random(seed * 1009 + idx))
            consider(gn, ge)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
