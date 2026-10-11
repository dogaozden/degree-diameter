import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Base: incidence graph of PG(2, q), points 0..m-1, lines m..2m-1, degree q+1.
# With d >= q+1 each vertex has spare s = d-q-1. Choose a point set S (indexed
# both as points and as lines) with every line holding <= s points of S and
# every point lying on <= s lines of S. Add a new X-vertex per P in S (joined
# to the q+1 lines through P) and a new Y-vertex per j in S (joined to the q+1
# points on line j). Diameter stays 3.
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
    """True if every line holds <= s points of S and every point lies on <= s lines of S."""
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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new X-vertex per P in S and a new Y-vertex per j in S."""
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


def _saturate(n, edges, m, k, d, rng):
    """Add every missing X-Y edge while both endpoints have spare degree (never lengthens distances)."""
    E = set()
    for u, v in edges:
        E.add((u, v) if u < v else (v, u))
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    X = [v for v in range(n) if v < m or 2 * m <= v < 2 * m + k]
    Y = [v for v in range(n) if m <= v < 2 * m or v >= 2 * m + k]
    spare_x = [v for v in X if deg[v] < d]
    spare_y = [v for v in Y if deg[v] < d]
    pairs = [(x, y) for x in spare_x for y in spare_y]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d:
            continue
        key = (x, y) if x < y else (y, x)
        if key in E:
            continue
        E.add(key)
        deg[x] += 1
        deg[y] += 1
    return n, sorted(E)


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, point_lines, line_points, index = _pg_data(q)
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
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, S)
        n_c, e_c = _saturate(n_c, e_c, m, len(S), d, rng)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q); diameter 4."""
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
# Growth by repair search (D = 3).
#
# Keep a valid bipartite graph. To add one X-vertex a and one Y-vertex b:
#  - take a matching M of d existing edges (x_i, y_i);
#  - replace each (x_i, y_i) by (a, y_i) and (x_i, b), so a and b reach degree d
#    and every old vertex keeps its degree;
#  - repair with degree-preserving bipartite 2-switches under simulated
#    annealing, minimizing the number of ordered pairs at distance > 3.
# Cost zero means a valid graph with two more vertices.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _cost(n, nb, D):
    """Ordered pairs at distance > D (zero iff diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal_switch(n, nb, E, deadline, rng, D=3):
    """Degree-preserving 2-switch annealing; mutates nb and E. Returns True iff cost reaches 0."""
    cost = _cost(n, nb, D)
    if cost == 0:
        return True
    m_e = len(E)
    if m_e < 2:
        return False
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    T0, T1 = 2.0, 0.1
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t_start) / span)
        i = rng.randrange(m_e)
        j = rng.randrange(m_e)
        if i == j:
            continue
        x1, y1 = E[i]
        x2, y2 = E[j]
        if x1 == x2 or y1 == y2 or y2 in nb[x1] or y1 in nb[x2]:
            continue
        nb[x1].discard(y1)
        nb[y1].discard(x1)
        nb[x2].discard(y2)
        nb[y2].discard(x2)
        nb[x1].add(y2)
        nb[y2].add(x1)
        nb[x2].add(y1)
        nb[y1].add(x2)
        c2 = _cost(n, nb, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            E[i] = (x1, y2)
            E[j] = (x2, y1)
        else:
            nb[x1].discard(y2)
            nb[y2].discard(x1)
            nb[x2].discard(y1)
            nb[y1].discard(x2)
            nb[x1].add(y1)
            nb[y1].add(x1)
            nb[x2].add(y2)
            nb[y2].add(x2)
    return cost == 0


def _try_extend(n, E, d, D, rng, deadline):
    """Try to add one X-vertex and one Y-vertex to the valid graph (n, E). Return (n+2, edges) or None."""
    a, b = n, n + 1
    N = n + 2
    nb = [set() for _ in range(N)]
    for x, y in E:
        nb[x].add(y)
        nb[y].add(x)
    idx = list(range(len(E)))
    rng.shuffle(idx)
    used_x, used_y = set(), set()
    M = []
    for i in idx:
        x, y = E[i]
        if x in used_x or y in used_y:
            continue
        M.append(i)
        used_x.add(x)
        used_y.add(y)
        if len(M) == d:
            break
    if len(M) < d:
        return None
    Mset = set(M)
    newE = [E[i] for i in range(len(E)) if i not in Mset]
    for i in M:
        x, y = E[i]
        nb[x].discard(y)
        nb[y].discard(x)
        nb[a].add(y)
        nb[y].add(a)
        nb[x].add(b)
        nb[b].add(x)
        newE.append((a, y))
        newE.append((x, b))
    if not _anneal_switch(N, nb, newE, deadline, rng, D):
        return None
    return N, newE


def _grow(n, edges, d, D, deadline, rng):
    """Repeatedly add a vertex pair while the repair search succeeds. Returns the best valid (n, edges)."""
    col = _two_color(n, edges)
    E = [(u, v) if col[u] == 0 else (v, u) for u, v in edges]
    best = (n, list(edges))
    cur_n = n
    while time.monotonic() < deadline - 1.0:
        res = _try_extend(cur_n, E, d, D, rng, deadline)
        if res is None:
            break
        cur_n, E = res
        best = (cur_n, list(E))
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(min(0.8 * time_limit, time_limit - 5.0), 0.4 * time_limit)
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    if D >= 3:
        for n_c, e_c in _arc_extensions(d, start + 0.25 * budget,
                                        random.Random(seed * 7919 + d)):
            if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
                best_n, best_e = n_c, e_c

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best_n and lib.is_valid(gq[0], gq[1], d, D):
            best_n, best_e = gq

    if D == 3 and best_n < lib.moore_bound(d, D) and time.monotonic() < deadline:
        gn, ge = _grow(best_n, best_e, d, D, deadline, rng)
        if gn > best_n and lib.is_valid(gn, ge, d, D):
            best_n, best_e = gn, ge

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
