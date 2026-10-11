import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Basic helpers
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
    """Return (m, edges, point_lines, line_points) for PG(2, q).

    Points are 0..m-1 and lines are indexed 0..m-1 (line j is the dual of point j).
    point_lines[P] lists the lines through P; line_points[j] lists the points on line j.
    """
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _conic_set(q, index):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _loads_ok(S, elem_cons, m, s):
    """True if every constraint (0..m-1) is touched by at most s elements of S."""
    cnt = [0] * m
    for i in S:
        for c in elem_cons[i]:
            cnt[c] += 1
    return max(cnt, default=0) <= s


# ----------------------------------------------------------------------------
# New helper: load-constrained local search.
#
# Element i touches a list of constraints elem_cons[i]. We want a large set of
# elements such that no constraint is touched more than s times. The search
# adds a random element when it is feasible, and otherwise performs a plateau
# swap when exactly one member blocks the element (the member lies on every
# saturated constraint of the candidate). This is a random walk over
# feasible sets; the best set seen is kept.
#
# For the twin construction, the side-0 twin set S0 uses constraints = lines
# (elem_cons = point_lines), and the side-1 twin set S1 uses constraints =
# points (elem_cons = line_points). The two sets are independent, so each is
# searched separately.
# ----------------------------------------------------------------------------

def _load_search(m, s, elem_cons, rng, t_end):
    n_el = len(elem_cons)
    load = [0] * m
    owners = [set() for _ in range(m)]
    cur = set()
    best = []
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > t_end:
            break
        i = rng.randrange(n_el)
        if i in cur:
            continue
        sat = [c for c in elem_cons[i] if load[c] >= s]
        if sat:
            inter = set(owners[sat[0]])
            for c in sat[1:]:
                inter &= owners[c]
            if len(inter) != 1 or rng.random() > 0.5:
                continue
            j = next(iter(inter))
            cur.discard(j)
            for c in elem_cons[j]:
                load[c] -= 1
                owners[c].discard(j)
        cur.add(i)
        for c in elem_cons[i]:
            load[c] += 1
            owners[c].add(i)
        if len(cur) > len(best):
            best = list(cur)
    return best


def _best_twin_sets(q, s, m, point_lines, line_points, index, rng, t_end):
    """Return (S0, S1): point set and line set for twins, each respecting load <= s."""
    S0, S1 = [], []
    if s >= 1:
        cand0 = [_load_search(m, s, point_lines, rng, t_end)]
        cand1 = [_load_search(m, s, line_points, rng, t_end)]
        if s >= 2:
            cs = _conic_set(q, index)
            cand0.append(cs)
            cand1.append(cs)
        S0 = max((c for c in cand0 if _loads_ok(c, point_lines, m, s)), key=len, default=[])
        S1 = max((c for c in cand1 if _loads_ok(c, line_points, m, s)), key=len, default=[])
    return S0, S1


def _twin_graph(m, edges, point_lines, line_points, S0, S1):
    """PG(2,q) incidence plus side-0 twins of points in S0 and side-1 twins of lines in S1.

    A twin of point P is adjacent to the lines through P. A twin of line j is adjacent
    to the points on j. Returns (n, edges, side).
    """
    k0, k1 = len(S0), len(S1)
    n = 2 * m + k0 + k1
    E = list(edges)
    for t, P in enumerate(S0):
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
    for t, j in enumerate(S1):
        b = 2 * m + k0 + t
        for Q in line_points[j]:
            E.append((Q, b))
    side = [0] * m + [1] * m + [0] * k0 + [1] * k1
    return n, E, side


def _twin_candidates(d, deadline, rng):
    """For each prime power q with q + 1 <= d, build the best twin-extended PG(2,q) graph."""
    qs = [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)]
    if not qs:
        return []
    weights = {q: q * q + q + 1 for q in qs}
    total_w = sum(weights.values())
    total_time = max(0.0, deadline - time.monotonic())
    out = []
    for q in qs:
        s = d - q - 1
        if s < 0:
            continue
        if time.monotonic() > deadline:
            break
        m, edges, point_lines, line_points = _pg_incidence(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        slice_t = total_time * weights[q] / total_w
        t_end = min(deadline, time.monotonic() + slice_t)
        S0, S1 = _best_twin_sets(q, s, m, point_lines, line_points, index, rng, t_end)
        n_c, E_c, side_c = _twin_graph(m, edges, point_lines, line_points, S0, S1)
        out.append((n_c, E_c, side_c))
    return out


# ----------------------------------------------------------------------------
# Degree-aware bipartite repair annealing (from parent).
# Starts from a valid twin graph, appends one vertex per side, and anneals
# to drive the number of pairs at distance > 3 to zero.
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


def _propose(adj, side0, side1, d, rng):
    """Return a list of ops ('a' add / 'd' delete) keeping max degree <= d, or None."""
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


def _repair(n, adj, side, d, D, rng, deadline):
    """Anneal until no pair is at distance > D. Returns True on success (adj updated in place)."""
    side0 = [v for v in range(n) if side[v] == 0]
    side1 = [v for v in range(n) if side[v] == 1]
    cost = _bad_pairs(n, adj, D)
    T = 1.5
    while cost > 0:
        if time.monotonic() > deadline:
            return False
        T = max(0.1, T * 0.999)
        ops = _propose(adj, side0, side1, d, rng)
        if ops is None:
            continue
        _apply(adj, ops)
        c2 = _bad_pairs(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            undo = [('d' if op == 'a' else 'a', x, y) for op, x, y in reversed(ops)]
            _apply(adj, undo)
    return True


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
    deadline = start + 0.75 * time_limit
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
        cands = _twin_candidates(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands:
            consider(n_c, E_c)
        if cands and lib.is_valid(cands[0][0], cands[0][1], d, D):
            arc_base = cands[0]

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Repair search for D = 3: add two vertices at a time (one per side) and
    # anneal to restore diameter 3. Each success becomes the next starting point.
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
            if not _repair(n_t, adj, side, d, D, rng, deadline):
                break
            E2 = [(x, y) for x in range(n_t) for y in adj[x] if x < y]
            if not lib.is_valid(n_t, E2, d, D):
                break
            consider(n_t, E2)
            n = n_t

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
