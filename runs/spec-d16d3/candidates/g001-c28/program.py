import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fallback: complete bipartite K_{d,d}. Diameter 2, degree d, valid for D >= 2.
# ----------------------------------------------------------------------------

def _complete_bipartite(d):
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Each old vertex has degree q+1 and spare capacity s = d - q - 1. Choose a
# point set S so that every line holds at most s points of S. For each P in S
# add an A-vertex joined to the q+1 lines through P; for each j in S add a
# B-vertex joined to the q+1 points on line j. Diameter stays 3.
# Order is 2(q^2+q+1) + 2|S|. For d=16 a conic (|S| = q+1 = 14, q=13) gives 394.
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
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in _LINE_POINTS[j]:
            E.append((Q, b))
    return n, E


_LINE_POINTS = None


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    global _LINE_POINTS
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        _LINE_POINTS = line_points
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4).
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
# Extension search: try to append new vertices to an existing valid graph.
# A new vertex goes on the side opposite its neighbours, so bipartiteness is
# kept. Neighbours are chosen among vertices with spare degree, greedily by
# how many new vertices they reach within two steps (with some randomness).
# Every addition is checked with lib.is_valid, so the graph is always valid.
# ----------------------------------------------------------------------------

def _extend(n, edges, d, D, rng, deadline):
    E = [(int(u), int(v)) for u, v in edges]
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)

    color = [-1] * n
    for s0 in range(n):
        if color[s0] != -1:
            continue
        color[s0] = 0
        stack = [s0]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)

    nb = [0] * n
    for v in range(n):
        mask = 0
        for u in adj[v]:
            mask |= 1 << u
        nb[v] = mask

    fails = 0
    while time.monotonic() < deadline and fails < 3000:
        side = rng.randrange(2)
        pool = [y for y in range(n) if color[y] == 1 - side and len(adj[y]) < d]
        if not pool:
            break
        k = min(d, len(pool))
        rng.shuffle(pool)
        remaining = pool
        covered = 0
        chosen = []
        for _ in range(k):
            if rng.random() < 0.2:
                idx = rng.randrange(len(remaining))
            else:
                idx = max(range(len(remaining)),
                          key=lambda i: (nb[remaining[i]] & ~covered).bit_count())
            y = remaining.pop(idx)
            chosen.append(y)
            covered |= nb[y]

        new = n
        E2 = E + [(y, new) for y in chosen]
        if lib.is_valid(new + 1, E2, d, D):
            E = E2
            n += 1
            adj.append(set(chosen))
            color.append(side)
            mask = 0
            for y in chosen:
                adj[y].add(new)
                nb[y] |= 1 << new
                mask |= 1 << y
            nb.append(mask)
            fails = 0
        else:
            fails += 1
    return n, E


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _complete_bipartite(d)

    # Arc-extended projective plane graphs: diameter 3, valid for all D >= 3.
    if D >= 3:
        arc_deadline = start + 0.3 * time_limit
        for n_c, e_c in _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d)):
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)

    # Generalized quadrangle: diameter 4, for D >= 4.
    if D >= 4 and time.monotonic() < start + 0.4 * time_limit:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
            best = gq

    # Spend the rest of the budget trying to append vertices to the best graph.
    if D >= 3 and time.monotonic() < start + 0.8 * time_limit:
        n_e, e_e = _extend(best[0], best[1], d, D, rng, start + 0.8 * time_limit)
        if n_e > best[0]:
            best = (n_e, e_e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = _complete_bipartite(d)
    return best
