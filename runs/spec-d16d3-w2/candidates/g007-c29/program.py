import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Moore bound and projective-plane arc constructions (as in the parent).
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
    """Incidence graph of PG(2,q) plus, per element of S, an A-vertex (pencil through it)
    and a B-vertex (joined to the points of the line). Returns (n, edges, side)."""
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
    """For each prime power q with q + 1 <= d, build the best arc-extended PG(2,q) graph."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points = _pg_incidence(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 60, deadline))
        if s >= 2:
            cs = _conic_set(q, index)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Bitmask ball helpers.
# ----------------------------------------------------------------------------

def _ball_masks(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        nxt = []
        for v in range(n):
            m = reach[v]
            for u in adj[v]:
                m |= reach[u]
            nxt.append(m)
        reach = nxt
    return reach


def _bad_count(n, reach):
    """Number of unordered pairs not reachable from each other (given radius-D masks)."""
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# NEW helper: coverage-greedy wiring of a fresh vertex.
#
# A new vertex v is joined to up to d vertices on `target` side that still
# have spare degree. Each step picks the candidate whose radius-(D-1) ball
# adds the most vertices to what v already reaches within distance D. This
# automatically finds pencil-like neighbourhoods (lines through a point cover
# all points) when they exist.
# ----------------------------------------------------------------------------

def _wire(n, adj, side, d, D, v, target, rng):
    cov = _ball_masks(n, adj, D - 1)
    cands = [y for y in range(n) if side[y] == target and y != v and len(adj[y]) < d]
    rng.shuffle(cands)
    reach = 1 << v
    while cands and len(adj[v]) < d:
        best, gain = None, 0
        for y in cands:
            g = (cov[y] & ~reach).bit_count()
            if g > gain:
                best, gain = y, g
        if best is None:
            break
        adj[v].add(best)
        adj[best].add(v)
        reach |= cov[best]
        cands.remove(best)


# ----------------------------------------------------------------------------
# Repair annealing with focused moves: pick an actually bad pair (u, v) and
# add an edge that creates a short path between them while respecting degree.
# ----------------------------------------------------------------------------

def _apply(adj, ops):
    for op, x, y in ops:
        if op == 'a':
            adj[x].add(y)
            adj[y].add(x)
        else:
            adj[x].discard(y)
            adj[y].discard(x)


def _undo(ops):
    return [('d' if op == 'a' else 'a', x, y) for op, x, y in reversed(ops)]


def _focus_move(adj, side, d, u, v, rng):
    """Edge-addition move that shortens a bad pair (u, v)."""
    if not adj[v] or len(adj[u]) >= d:
        return None
    z = rng.choice(list(adj[v]))
    if side[u] != side[v]:
        # Path u - w - z - v of length 3 with w in N(z).
        cands = [w for w in adj[z] if w != u and w not in adj[u] and len(adj[w]) < d]
        if not cands:
            return None
        return [('a', u, rng.choice(cands))]
    # Same side: path u - z - v of length 2 with z in N(v).
    if z in adj[u] or len(adj[z]) >= d:
        return None
    return [('a', u, z)]


def _propose(adj, side0, side1, d, rng):
    """Random degree-respecting move (2-opt swap, single add, or endpoint shift)."""
    r = rng.random()
    if r < 0.6:
        x1 = rng.choice(side0)
        x2 = rng.choice(side0)
        if x1 == x2 or not adj[x1] or not adj[x2]:
            return None
        y1 = rng.choice(list(adj[x1]))
        y2 = rng.choice(list(adj[x2]))
        if y1 == y2 or y2 in adj[x1] or y1 in adj[x2]:
            return None
        return [('d', x1, y1), ('d', x2, y2), ('a', x1, y2), ('a', x2, y1)]
    if r < 0.8:
        x = rng.choice(side0)
        y = rng.choice(side1)
        if y in adj[x] or len(adj[x]) >= d or len(adj[y]) >= d:
            return None
        return [('a', x, y)]
    x1 = rng.choice(side0)
    if not adj[x1]:
        return None
    y1 = rng.choice(list(adj[x1]))
    if rng.random() < 0.5:
        y2 = rng.choice(side1)
        if y2 == y1 or y2 in adj[x1] or len(adj[y2]) >= d:
            return None
        return [('d', x1, y1), ('a', x1, y2)]
    x2 = rng.choice(side0)
    if x2 == x1 or y1 in adj[x2] or len(adj[x2]) >= d:
        return None
    return [('d', x1, y1), ('a', x2, y1)]


def _repair(n, adj, side, d, D, rng, deadline, budget):
    """Anneal until no pair is at distance > D. Adjacency is updated in place."""
    side0 = [v for v in range(n) if side[v] == 0]
    side1 = [v for v in range(n) if side[v] == 1]
    full = (1 << n) - 1
    reach = _ball_masks(n, adj, D)
    cost = _bad_count(n, reach)
    T = 0.8
    for _ in range(budget):
        if cost == 0:
            return True
        if time.monotonic() > deadline:
            return False
        T = max(0.05, T * 0.995)
        bad_u = [u for u in range(n) if reach[u] != full]
        u = rng.choice(bad_u)
        miss = full & ~reach[u]
        vs = [v for v in range(n) if (miss >> v) & 1]
        v = rng.choice(vs)
        if rng.random() < 0.85:
            ops = _focus_move(adj, side, d, u, v, rng)
        else:
            ops = _propose(adj, side0, side1, d, rng)
        if ops is None:
            continue
        _apply(adj, ops)
        r2 = _ball_masks(n, adj, D)
        c2 = _bad_count(n, r2)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost, reach = c2, r2
        else:
            _apply(adj, _undo(ops))
    return cost == 0


def _extend(n, adj, side, d, D, rng, deadline, budget):
    """Add one A-vertex (side 0) and one B-vertex (side 1), wire them greedily, then repair.
    Returns (n2, adj2, side2) or None. The input graph is never modified."""
    n2 = n + 2
    adj2 = [set(s) for s in adj] + [set(), set()]
    side2 = list(side) + [0, 1]
    a, b = n, n + 1
    _wire(n2, adj2, side2, d, D, a, 1, rng)
    _wire(n2, adj2, side2, d, D, b, 0, rng)
    if not _repair(n2, adj2, side2, d, D, rng, deadline, budget):
        return None
    return n2, adj2, side2


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4), unchanged from parent.
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

    arc_base = None
    if D >= 3:
        cands = _arc_candidates(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands:
            consider(n_c, E_c)
        if cands and lib.is_valid(cands[0][0], cands[0][1], d, D):
            arc_base = cands[0]

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # D = 3: repeatedly extend the current valid graph by one A/B pair.
    if D == 3 and arc_base is not None:
        n, E, side = arc_base
        adj = [set() for _ in range(n)]
        for u, v in E:
            adj[u].add(v)
            adj[v].add(u)
        cur_n, cur_adj, cur_side = n, adj, list(side)
        while time.monotonic() < deadline and cur_n + 2 <= _moore(d, D):
            if not any(len(cur_adj[x]) < d for x in range(cur_n)):
                break
            res = _extend(cur_n, cur_adj, cur_side, d, D, rng, deadline, 300)
            if res is None:
                continue
            n2, adj2, side2 = res
            E2 = [(x, y) for x in range(n2) for y in adj2[x] if x < y]
            if not lib.is_valid(n2, E2, d, D):
                continue
            consider(n2, E2)
            cur_n, cur_adj, cur_side = n2, adj2, side2

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
