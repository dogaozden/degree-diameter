import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc construction (safe base for D = 3)
# ----------------------------------------------------------------------------

def _pg_incidence(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points 0..m-1, lines 0..m-1."""
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
    """Incidence graph of PG(2,q) plus an A-vertex and a B-vertex per element of S. Returns (n, E, side)."""
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
    """For each prime power q with q + 1 <= d, build the arc-extended PG(2,q) graph."""
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
# Bold change for D = 3: grow the arc graph by two vertices (one per side) and
# repair with simulated annealing on the number of pairs at distance > 3.
#
# Moves keep the graph bipartite and every degree <= d:
#   - add an edge between two spare-degree vertices on opposite sides,
#   - a degree-preserving 2-switch,
#   - remove an edge (diversification).
# Cost = number of ordered pairs at distance > 3 (zero means diameter <= 3).
# ----------------------------------------------------------------------------

def _cost(n, adj):
    """Number of ordered vertex pairs at distance > 3."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(n - r.bit_count() for r in reach)


def _anneal(n, side, adj, d, deadline, rng):
    """Anneal adj (list of sets) until cost 0 or deadline. Returns True if diameter <= 3 was reached."""
    A = [v for v in range(n) if side[v] == 0]
    B = [v for v in range(n) if side[v] == 1]
    cur = _cost(n, adj)
    T = 1.0
    it = 0
    while cur > 0 and time.monotonic() < deadline:
        it += 1
        if it % 2000 == 0:
            T = 1.0  # reheat to escape stagnation
        T = max(0.05, T * 0.999)
        r = rng.random()
        if r < 0.35:
            sa = [a for a in A if len(adj[a]) < d]
            sb = [b for b in B if len(adj[b]) < d]
            if not sa or not sb:
                continue
            a = rng.choice(sa)
            b = rng.choice(sb)
            if b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            new = _cost(n, adj)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                adj[a].discard(b)
                adj[b].discard(a)
        elif r < 0.9:
            a1 = rng.choice(A)
            if not adj[a1]:
                continue
            b1 = rng.choice(list(adj[a1]))
            b2 = rng.choice(B)
            if not adj[b2]:
                continue
            a2 = rng.choice(list(adj[b2]))
            if a1 == a2 or b1 == b2 or b2 in adj[a1] or a2 in adj[b1]:
                continue
            adj[a1].discard(b1)
            adj[b1].discard(a1)
            adj[a2].discard(b2)
            adj[b2].discard(a2)
            adj[a1].add(b2)
            adj[b2].add(a1)
            adj[a2].add(b1)
            adj[b1].add(a2)
            new = _cost(n, adj)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                adj[a1].discard(b2)
                adj[b2].discard(a1)
                adj[a2].discard(b1)
                adj[b1].discard(a2)
                adj[a1].add(b1)
                adj[b1].add(a1)
                adj[a2].add(b2)
                adj[b2].add(a2)
        else:
            a = rng.choice(A)
            if not adj[a]:
                continue
            b = rng.choice(list(adj[a]))
            adj[a].discard(b)
            adj[b].discard(a)
            new = _cost(n, adj)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                adj[a].add(b)
                adj[b].add(a)
    return cur == 0


def _grow_from(n0, E0, side0, d, D, deadline, rng):
    """Add one A-vertex and one B-vertex to the base graph and anneal. Returns (n, E) or None."""
    n = n0 + 2
    if n > lib.moore_bound(d, D):
        return None
    adj = [set() for _ in range(n)]
    for u, v in E0:
        adj[u].add(v)
        adj[v].add(u)
    side = list(side0) + [0, 1]
    if not _anneal(n, side, adj, d, deadline, rng):
        return None
    E = [(a, b) for a in range(n) if side[a] == 0 for b in adj[a]]
    return n, E


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
    budget = min(0.7 * float(time_limit), 40.0)
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 17 * d + D)

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

    if D == 3 and d >= 2:
        cands = _arc_candidates(d, start + 0.25 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        if cands:
            n0, E0, side0 = cands[0]
            consider(n0, E0)
            res = _grow_from(n0, E0, side0, d, D, deadline, rng)
            if res is not None:
                consider(*res)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
