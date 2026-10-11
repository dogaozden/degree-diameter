import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the point-line incidence graph of PG(2, q): points 0..m-1 (side 0),
# lines m..2m-1 (side 1). Each old vertex has degree q+1, so spare s = d-q-1.
# An arc S (each line holds <= s points of S, each point lies on <= s lines
# indexed by S) lets us add an A-vertex (side 0) per P in S joined to the lines
# through P, and a B-vertex (side 1) per j in S joined to the points on line j.
#
# NEW in this version: stub-growth search on top of the arc graph.
#   * Vertex insertion: a new vertex of one side is joined to up to d spare
#     vertices of the opposite side. It is kept only if the diameter is still
#     <= D. Bipartiteness and degrees hold by construction.
#   * Free edge completion: adding an edge between opposite sides never breaks
#     the diameter bound, so spare stubs are sometimes spent on edges that
#     shorten distances and make later vertex insertions feasible.
#   * Ejection: remove a vertex only if the remaining graph still has diameter
#     <= D. This frees up d stubs on its neighbours. The search restores the
#     best snapshot if it drifts too far below it.
# Every state stays valid, and the best snapshot is returned.
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


def _arc_graph(m, edges, S, point_lines, line_points):
    """Extended graph plus side labels (0 = point/A side, 1 = line/B side)."""
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
    side = [0] * n
    for v in range(m, 2 * m):
        side[v] = 1
    for v in range(2 * m + k, n):
        side[v] = 1
    return n, E, side


def _arc_extensions(d, deadline, rng):
    """Return candidates (n, edges, side) for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, pl, lp):
            continue
        n_c, E_c, side = _arc_graph(m, edges, S, pl, lp)
        out.append((n_c, E_c, side))
    return out


# ----------------------------------------------------------------------------
# Graph state helpers. adj is a list of sets, side a list of 0/1.
# ----------------------------------------------------------------------------

def _diam_ok(adj, D):
    """True if every pair of vertices is at distance <= D (adj has no dead slots)."""
    n = len(adj)
    full = (1 << n) - 1
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
        if all(r == full for r in reach):
            return True
    return all(r == full for r in reach)


def _snapshot(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _load(E, n):
    a = [set() for _ in range(n)]
    for u, v in E:
        a[u].add(v)
        a[v].add(u)
    return a


def _remove_vertex(adj, side, w):
    """Return a compacted copy of the graph with vertex w deleted."""
    n = len(adj)
    mp = {}
    j = 0
    for v in range(n):
        if v != w:
            mp[v] = j
            j += 1
    na = [set() for _ in range(j)]
    ns = [0] * j
    for v in range(n):
        if v == w:
            continue
        ns[mp[v]] = side[v]
        na[mp[v]] = {mp[u] for u in adj[v] if u != w}
    return na, ns


def _grow(adj, side, d, D, deadline, rng):
    """Stub-growth search with diameter-checked vertex insertion. Returns (n, edges) of the best state."""
    best_n = len(adj)
    best_E = _snapshot(adj)
    best_side = list(side)
    stuck = 0

    while time.monotonic() < deadline:
        n = len(adj)
        spare = [[], []]
        for u in range(n):
            if len(adj[u]) < d:
                spare[side[u]].append(u)
        if not spare[0] and not spare[1]:
            break

        # Vertex insertion: new vertex of side c joins spare vertices of side 1-c.
        c = rng.randrange(2)
        if not spare[1 - c]:
            c = 1 - c
        cands = spare[1 - c]
        k = min(d, len(cands))
        if k >= 3 and rng.random() < 0.3:
            k = rng.randint(2, k)
        nb = rng.sample(cands, k)

        w = n
        adj.append(set(nb))
        side.append(c)
        for u in nb:
            adj[u].add(w)
        if _diam_ok(adj, D):
            stuck = 0
            if n + 1 > best_n:
                best_n = n + 1
                best_E = _snapshot(adj)
                best_side = list(side)
            continue
        for u in nb:
            adj[u].discard(w)
        adj.pop()
        side.pop()

        # Free edge completion: never breaks the diameter bound.
        stuck += 1
        if rng.random() < 0.2 and spare[0] and spare[1]:
            u = rng.choice(spare[0])
            v = rng.choice(spare[1])
            if u != v and v not in adj[u] and len(adj[u]) < d and len(adj[v]) < d:
                adj[u].add(v)
                adj[v].add(u)

        if stuck >= 60:
            stuck = 0
            if len(adj) < best_n - 3:
                adj = _load(best_E, best_n)
                side = list(best_side)
            else:
                nn = len(adj)
                for _ in range(20):
                    w2 = rng.randrange(nn)
                    a2, s2 = _remove_vertex(adj, side, w2)
                    if _diam_ok(a2, D):
                        adj, side = a2, s2
                        break

    return best_n, best_E


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

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
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
            best = (n, e)
            best_n = n

    if D >= 3:
        cands = _arc_extensions(d, start + 0.2 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        if cands:
            consider(cands[0][0], cands[0][1])

        grow_list = cands[:2]
        if grow_list:
            share = max(0.0, deadline - time.monotonic()) / len(grow_list)
            for idx, (n_c, E_c, side) in enumerate(grow_list):
                adj = _load(E_c, n_c)
                if not _diam_ok(adj, D):
                    continue
                gdl = min(deadline, time.monotonic() + share)
                res_n, res_E = _grow(adj, list(side), d, D, gdl,
                                     random.Random(seed * 131 + idx))
                consider(res_n, res_E)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
