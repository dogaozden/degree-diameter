import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc extensions (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Pick a point set S with
# every line holding <= s points of S and every point on <= s lines indexed by
# S. Each P in S gets a new A-vertex joined to the q+1 lines through P; each
# j in S gets a new B-vertex joined to the q+1 points on line j.
# ----------------------------------------------------------------------------

def _pg_data(q):
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, S, line_points):
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


def _arc_candidates(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, S, line_points))
    return out


# ----------------------------------------------------------------------------
# Helpers
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
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


def _fill(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover the opposite side (exact-checked)."""
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 300:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        col = _bipartition(n, adj)
        c = rng.randrange(2)
        uncovered = {v for v in range(n) if col[v] == 1 - c}
        cand = [v for v in range(n) if col[v] == c and deg[v] < d]
        chosen = []
        chosen_set = set()
        while uncovered and len(chosen) < d:
            best_v = None
            best_key = None
            for v in cand:
                if v in chosen_set:
                    continue
                g = sum(1 for u in adj[v] if u in uncovered)
                if g == 0:
                    continue
                key = (g, rng.random())
                if best_key is None or key > best_key:
                    best_key = key
                    best_v = v
            if best_v is None:
                break
            chosen.append(best_v)
            chosen_set.add(best_v)
            for u in adj[best_v]:
                uncovered.discard(u)
        if uncovered:
            fails += 1
            continue
        new_edges = edges + [(v, n) for v in chosen]
        if lib.is_valid(n + 1, new_edges, d, D):
            edges = new_edges
            n += 1
            fails = 0
        else:
            fails += 1
    return n, edges


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used only when D >= 4.
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
# NEW construction stage: simulated annealing over bipartite edge sets.
#
# Start from a valid graph, add vertices, and let annealing repair diameter.
# Moves keep the graph bipartite and degree <= d:
#   - swap: (a,b),(c,e) -> (a,e),(c,b) (degree preserving),
#   - add an edge between spare-degree vertices on opposite sides,
#   - remove an edge.
# Cost = number of vertex pairs at distance > D. When cost hits 0 we record
# the graph and grow it by one A-vertex and one B-vertex.
# ----------------------------------------------------------------------------

def _grow(n, col, E, S, deg, d, rng):
    x, y = n, n + 1
    col = col + [0, 1]
    deg = deg + [0, 0]
    E = list(E)
    S = set(S)
    cand1 = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    cand0 = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    rng.shuffle(cand1)
    rng.shuffle(cand0)
    for v in cand1[:d]:
        E.append((x, v))
        S.add((x, v))
        deg[x] += 1
        deg[v] += 1
    for v in cand0[:d]:
        E.append((v, y))
        S.add((v, y))
        deg[y] += 1
        deg[v] += 1
    return n + 2, col, E, S, deg


def _sa_grow(n, edges, d, D, deadline, rng, best_n, best_e):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = _bipartition(n, adj)
    E = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]
    S = set(E)
    deg = [0] * n
    for a, b in E:
        deg[a] += 1
        deg[b] += 1
    cost = lib.bad_pairs(n, E, D)
    T = 1.0

    while time.monotonic() < deadline:
        if cost == 0:
            if n > best_n and lib.is_valid(n, E, d, D):
                best_n, best_e = n, list(E)
            n, col, E, S, deg = _grow(n, col, E, S, deg, d, rng)
            cost = lib.bad_pairs(n, E, D)
            T = 1.0
            continue

        r = rng.random()
        if r < 0.6:
            m = len(E)
            if m < 2:
                continue
            i = rng.randrange(m)
            j = rng.randrange(m)
            if i == j:
                continue
            a, b = E[i]
            c, e = E[j]
            if a == c or b == e or (a, e) in S or (c, b) in S:
                continue
            E2 = list(E)
            E2[i] = (a, e)
            E2[j] = (c, b)
            S2 = (S - {(a, b), (c, e)}) | {(a, e), (c, b)}
            deg2 = deg
        elif r < 0.8:
            xs = [v for v in range(n) if col[v] == 0 and deg[v] < d]
            ys = [v for v in range(n) if col[v] == 1 and deg[v] < d]
            if not xs or not ys:
                continue
            x = rng.choice(xs)
            y = rng.choice(ys)
            if (x, y) in S:
                continue
            E2 = E + [(x, y)]
            S2 = S | {(x, y)}
            deg2 = list(deg)
            deg2[x] += 1
            deg2[y] += 1
        else:
            if not E:
                continue
            idx = rng.randrange(len(E))
            a, b = E[idx]
            E2 = E[:idx] + E[idx + 1:]
            S2 = S - {(a, b)}
            deg2 = list(deg)
            deg2[a] -= 1
            deg2[b] -= 1

        c2 = lib.bad_pairs(n, E2, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            E, S, deg, cost = E2, S2, deg2, c2
        T = max(0.15, T * 0.9995)

    return best_n, best_e


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D >= 3:
        for n_c, e_c in _arc_candidates(d, start + 0.3 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

        if best_n > 2 and time.monotonic() < start + 0.45 * time_limit:
            n_f, e_f = _fill(best_n, best[1], d, D, start + 0.45 * time_limit,
                             random.Random(seed * 104729 + d))
            consider(n_f, e_f)

        if best_n > 2 and time.monotonic() < deadline:
            n_s, e_s = _sa_grow(best_n, best[1], d, D, deadline, rng, best_n, best[1])
            consider(n_s, e_s)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
