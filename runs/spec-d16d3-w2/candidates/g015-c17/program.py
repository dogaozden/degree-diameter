import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Helpers
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
    """Incidence graph of PG(2,q) plus, per element of S, an A-vertex (on lines through it)
    and a B-vertex (joined to points of the line). Returns (n, edges, side)."""
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
# Bipartite repair annealing, now with targeted moves.
#
# Each step picks a random pair (v, u) at distance > 3 and proposes a move that
# directly creates a short path between them:
#   * same side: add a common neighbour w on the opposite side (edges v-w, u-w);
#   * opposite side: add edge v-u, or an edge x-y with x in N(v), y in N(u).
# If an endpoint is saturated at degree d, a random non-touched incident edge is
# removed to make room. Moves keep the graph bipartite and max degree <= d, and
# are accepted by Metropolis on the number of bad pairs.
# ----------------------------------------------------------------------------

def _to_adj(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _balls(n, adj, D):
    """Bitmask of vertices within distance D of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return reach


def _cost(n, reach):
    """Number of unordered pairs at distance > D, given the ball bitmasks."""
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


def _targeted_ops(adj, side, side0, side1, d, rng, v, u):
    """Ops that try to bring the bad pair (v, u) within distance 3, or None."""
    if side[v] == side[u]:
        opp = side1 if side[v] == 0 else side0
        w = rng.choice(opp)
        if w in adj[v] or w in adj[u]:
            return None
        adds = [(v, w), (u, w)]
    else:
        if u in adj[v]:
            return None
        if adj[v] and adj[u] and rng.random() < 0.5:
            x = rng.choice(list(adj[v]))
            y = rng.choice(list(adj[u]))
            if y in adj[x]:
                return None
            adds = [(x, y)]
        else:
            adds = [(v, u)]

    need = {}
    for a, b in adds:
        need[a] = need.get(a, 0) + 1
        need[b] = need.get(b, 0) + 1
    touched = set(need)

    ops = []
    for e, k in need.items():
        over = len(adj[e]) + k - d
        if over > 0:
            cands = [z for z in adj[e] if z not in touched]
            if len(cands) < over:
                return None
            for z in rng.sample(cands, over):
                ops.append(('d', e, z))
    for a, b in adds:
        ops.append(('a', a, b))
    return ops


def _repair(n, adj, side, side0, side1, d, D, rng, deadline):
    """Anneal until no pair is at distance > D. Returns True on success (adj updated in place)."""
    reach = _balls(n, adj, D)
    cost = _cost(n, reach)
    T = 1.0
    while cost > 0:
        if time.monotonic() > deadline:
            return False
        T = max(0.05, T * 0.9995)

        bad_vs = [x for x in range(n) if reach[x].bit_count() < n]
        v = rng.choice(bad_vs)
        miss = [x for x in range(n) if x != v and not (reach[v] >> x) & 1]
        u = rng.choice(miss)

        ops = _targeted_ops(adj, side, side0, side1, d, rng, v, u)
        if ops is None:
            continue
        _apply(adj, ops)
        new_reach = _balls(n, adj, D)
        c2 = _cost(n, new_reach)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            reach = new_reach
        else:
            _apply(adj, _undo_ops(ops))
    return True


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

    # D = 3: add two vertices at a time (one per side) and repair with targeted
    # annealing. Each success becomes the next starting point.
    if D == 3 and arc_base is not None:
        n, E, side = arc_base
        adj = _to_adj(n, E)
        side = list(side)
        while time.monotonic() < deadline:
            n_t = n + 2
            if n_t > _moore(d, D):
                break
            adj.append(set())
            adj.append(set())
            side = side + [0, 1]
            side0 = [x for x in range(n_t) if side[x] == 0]
            side1 = [x for x in range(n_t) if side[x] == 1]
            if not _repair(n_t, adj, side, side0, side1, d, D, rng, deadline):
                break
            E2 = [(x, y) for x in range(n_t) for y in adj[x] if x < y]
            if not lib.is_valid(n_t, E2, d, D):
                break
            consider(n_t, E2)
            n = n_t

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
