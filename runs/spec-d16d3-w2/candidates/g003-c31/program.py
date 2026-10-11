import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Moore bound and projective-plane arc construction (D = 3)
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _pg_incidence(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points 0..m-1, lines indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


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
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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


def _conic_set(q, index):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Incidence graph of PG(2,q) plus, per element of S, an A-vertex (pencil at that point)
    and a B-vertex (dual pencil on that line). Returns (n, edges, side).
    Vertices: points 0..m-1, lines m..2m-1, A-vertices 2m.., B-vertices 2m+k.. ."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _arc_candidates(d, deadline, rng):
    """For each prime power q with q + 1 <= d, build the best arc-extended PG(2,q) graph.
    Returns tuples (n, E, side, m, point_lines, line_points)."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp = _pg_incidence(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 60, deadline))
        if s >= 2:
            cs = _conic_set(q, index)
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        n, E, side = _arc_graph(m, edges, pl, lp, S)
        out.append((n, E, side, m, pl, lp))
    return out


# ----------------------------------------------------------------------------
# Adjacency helpers
# ----------------------------------------------------------------------------

def _to_adj(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _bad_pairs(n, adj, D):
    """Unordered pairs at distance > D, via bitmask balls."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _apply(adj, ops):
    for op, x, y in ops:
        if op == 'a':
            adj[x].add(y)
            adj[y].add(x)
        else:
            adj[x].discard(y)
            adj[y].discard(x)


def _undo_ops(ops):
    return [('d' if op == 'a' else 'a', x, y) for op, x, y in reversed(ops)]


# ----------------------------------------------------------------------------
# New helper: pencil/dual-pencil insertion with deletion repair and annealing.
#
# Appending an A-vertex whose neighbourhood is the full pencil of lines through
# a point P (and a B-vertex on the points of a line j) makes every pair of new
# vertices and every old vertex at distance <= 3 in an intact PG(2,q) structure.
# The only obstacle is degree: pencil lines that are already full must shed an
# edge. We pick P and j that minimise the number of full neighbours, delete
# excess edges, greedily fill spare capacity (adding edges never increases the
# bad-pair count), and then anneal with degree-preserving 2-switches until the
# diameter is restored. Only validated graphs are kept.
# ----------------------------------------------------------------------------

def _pick_point(adj, m, point_lines, d, rng):
    best, bestc = None, None
    for P in rng.sample(range(m), min(m, 48)):
        c = sum(1 for L in point_lines[P] if len(adj[m + L]) >= d)
        if bestc is None or c < bestc:
            best, bestc = P, c
            if c == 0:
                break
    return best


def _pick_line(adj, m, line_points, d, rng):
    best, bestc = None, None
    for L in rng.sample(range(m), min(m, 48)):
        c = sum(1 for Q in line_points[L] if len(adj[Q]) >= d)
        if bestc is None or c < bestc:
            best, bestc = L, c
            if c == 0:
                break
    return best


def _grow_two(n, adj, side, m, point_lines, line_points, d, rng):
    """Append an A-vertex (pencil at a point) and a B-vertex (dual pencil on a line)."""
    P = _pick_point(adj, m, point_lines, d, rng)
    j = _pick_line(adj, m, line_points, d, rng)
    a, b = n, n + 1
    adj.append(set())
    adj.append(set())
    side.append(0)
    side.append(1)
    touched = []
    for L in point_lines[P]:
        v = m + L
        adj[a].add(v)
        adj[v].add(a)
        touched.append(v)
    for Q in line_points[j]:
        adj[b].add(Q)
        adj[Q].add(b)
        touched.append(Q)
    for v in touched:
        while len(adj[v]) > d:
            cands = [w for w in adj[v] if w != a and w != b]
            if not cands:
                break
            w = rng.choice(cands)
            adj[v].discard(w)
            adj[w].discard(v)


def _fill(n, adj, side, d):
    """Greedily add edges between spare-capacity vertices of opposite sides."""
    s0 = [v for v in range(n) if side[v] == 0 and len(adj[v]) < d]
    s1 = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
    for x in s0:
        if len(adj[x]) >= d:
            continue
        for y in s1:
            if len(adj[x]) >= d:
                break
            if len(adj[y]) < d and y not in adj[x]:
                adj[x].add(y)
                adj[y].add(x)


def _move(adj, side0, side1, d, rng):
    """Degree-preserving 2-switch, or an addition between spare-capacity vertices."""
    if rng.random() < 0.25:
        x = rng.choice(side0)
        y = rng.choice(side1)
        if y in adj[x] or len(adj[x]) >= d or len(adj[y]) >= d:
            return None
        return [('a', x, y)]
    x1 = rng.choice(side0)
    x2 = rng.choice(side0)
    if x1 == x2 or not adj[x1] or not adj[x2]:
        return None
    y1 = rng.choice(tuple(adj[x1]))
    y2 = rng.choice(tuple(adj[x2]))
    if y1 == y2 or y2 in adj[x1] or y1 in adj[x2]:
        return None
    return [('d', x1, y1), ('d', x2, y2), ('a', x1, y2), ('a', x2, y1)]


def _anneal(n, adj, side, d, D, rng, deadline, iters):
    """Anneal until bad pairs vanish. Returns the final bad-pair count (0 on success)."""
    side0 = [v for v in range(n) if side[v] == 0]
    side1 = [v for v in range(n) if side[v] == 1]
    cost = _bad_pairs(n, adj, D)
    T = 0.8
    for _ in range(iters):
        if cost == 0:
            break
        if time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.99)
        ops = _move(adj, side0, side1, d, rng)
        if ops is None:
            continue
        _apply(adj, ops)
        c2 = _bad_pairs(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _apply(adj, _undo_ops(ops))
    return cost


def _extend(n, adj, side, m, pl, lp, d, D, rng, deadline, consider):
    """Repeatedly try to add two vertices (one per side) and keep every validated success."""
    while time.monotonic() < deadline and n + 2 <= _moore(d, D):
        trial = [set(s) for s in adj]
        tside = list(side)
        _grow_two(n, trial, tside, m, pl, lp, d, rng)
        _fill(n + 2, trial, tside, d)
        cost = _anneal(n + 2, trial, tside, d, D, rng, deadline, 220)
        if cost == 0:
            E = [(x, y) for x in range(n + 2) for y in trial[x] if x < y]
            if lib.is_valid(n + 2, E, d, D):
                consider(n + 2, E)
                adj, side, n = trial, tside, n + 2


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4)
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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
            best_n, best_E = n, E

    cands = []
    if D >= 3:
        cands = _arc_candidates(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for c in cands:
            consider(c[0], c[1])

    # D = 3: grow the best arc-extended PG(2,q) graph with pencil insertions.
    if D == 3 and cands:
        n, E, side, m, pl, lp = cands[0]
        if lib.is_valid(n, E, d, D):
            adj = _to_adj(n, E)
            _extend(n, adj, list(side), m, pl, lp, d, D,
                    random.Random(seed * 104729 + d), deadline, consider)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
