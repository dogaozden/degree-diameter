import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane data and arc-extended incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d-q-1. A point set S with every
# line holding <= s points of S, and every point on <= s lines indexed by S,
# supports one new A-vertex per point of S and one new B-vertex per line of S.
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


def _random_arc(m, s, point_lines, line_points, rng):
    """One randomized greedy choice of S with all loads <= s."""
    order = list(range(m))
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
    return S


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG incidence plus a new A-vertex per point of S and a new B-vertex per line of S."""
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
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

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
# NEW: cover-greedy vertex insertion.
#
# A new vertex X of colour c joins a set T of vertices of the opposite colour,
# |T| <= d, which must have spare degree. X reaches every existing vertex within
# D iff the radius-(D-1) balls of T cover the whole graph. So we grow the graph
# by repeatedly choosing T greedily by coverage gain (bitmask set cover), adding
# X, and keeping the step only if lib.is_valid still passes. This can absorb
# spare capacity that the arc construction leaves on points and lines.
# ----------------------------------------------------------------------------

def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return reach


def _two_color(n, adj):
    """Proper 2-colouring of a bipartite graph (components coloured independently)."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _grow(n, E, d, D, rng, deadline, patience):
    """Greedily insert new vertices while the graph stays valid; return best (n, edges) seen."""
    E = list(E)
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _two_color(n, adj)
    ball = _balls(n, adj, D - 1)
    best = (n, list(E))
    fails = 0
    while fails < patience and time.monotonic() < deadline:
        full = (1 << n) - 1
        k = rng.randrange(2)
        pool = [v for v in range(n) if color[v] == k and deg[v] < d]
        T = []
        covered = 0
        while covered != full and len(T) < d:
            bg = 0
            cands = []
            for v in pool:
                g = (ball[v] & ~covered).bit_count()
                if g > bg:
                    bg = g
                    cands = [v]
                elif g == bg and g > 0:
                    cands.append(v)
            if bg == 0:
                break
            v = rng.choice(cands)
            T.append(v)
            covered |= ball[v]
        if covered != full or not T:
            fails += 1
            continue
        x = n
        adj.append(list(T))
        deg.append(len(T))
        color.append(1 - k)
        for t in T:
            adj[t].append(x)
            deg[t] += 1
            E.append((t, x))
        if lib.is_valid(n + 1, E, d, D):
            n += 1
            best = (n, list(E))
            ball = _balls(n, adj, D - 1)
            fails = 0
        else:
            for t in T:
                adj[t].pop()
                deg[t] -= 1
            del E[len(E) - len(T):]
            adj.pop()
            deg.pop()
            color.pop()
            fails += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    bases = [(best_n, list(best_E))]
    try:
        if D >= 3:
            qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]
            for q in reversed(qs):
                if time.monotonic() > deadline:
                    break
                m, edges, pl, lp, index = _pg_data(q)
                s = d - q - 1
                # Plain projective-plane incidence graph: diameter 3, degree q+1.
                plain = (2 * m, list(edges))
                bases.append(plain)
                consider(*plain)
                if s >= 1:
                    cands = []
                    if s >= 2:
                        F = lib.GF(q)
                        cs = _conic_set(q, index, F)
                        if _loads_ok(cs, s, m, pl, lp):
                            cands.append(cs)
                    for _ in range(6):
                        cands.append(_random_arc(m, s, pl, lp, rng))
                    for S in cands:
                        if S and _loads_ok(S, s, m, pl, lp):
                            g = _arc_graph(m, edges, pl, lp, S)
                            bases.append(g)
                            consider(*g)

        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                bases.append(gq)
                consider(*gq)

        bases.sort(key=lambda t: -t[0])
        # Grow each of the strongest bases once, then keep sampling growth runs.
        for base in bases[:3]:
            if time.monotonic() > deadline:
                break
            g = _grow(base[0], base[1], d, D, rng, deadline, patience=150)
            consider(*g)

        stall = 0
        while time.monotonic() < deadline and stall < 8:
            base = bases[rng.randrange(min(len(bases), 6))]
            g = _grow(base[0], base[1], d, D, rng, deadline, patience=150)
            if g[0] > best_n:
                consider(*g)
                stall = 0
            else:
                stall += 1
    except Exception:
        pass

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, best_E
