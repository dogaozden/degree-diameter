"""Arc-extended projective plane graphs (diameter 3) with a greedy, oracle-checked augmentation.

Base: incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1), every vertex of degree q+1.
With s = d - q - 1 spare slots per vertex, a point set S with at most s points on each line
gives new A-vertices (joined to the pencil of lines through each point of S) and new
B-vertices (joined to the points of each line in S). The graph stays at diameter 3.

New routine (_augment): before saturation, repeatedly propose a new vertex on either side.
Its neighbours are chosen by greedy set cover over same-side vertices, so every same-side
vertex is within distance 2. Each proposal is accepted only if lib.is_valid still holds.
This can add vertices beyond the pencil construction whenever spare capacity is arranged well.
Saturation (X-Y edges between spare vertices) is applied last and validated.
"""
import random
import time

import lib


def _key(u, v):
    return (u, v) if u < v else (v, u)


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
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_base(m, edges, point_lines, line_points, S):
    """Base graph: PG incidence plus a new A-vertex per point of S and a new B-vertex per line of S.

    Sides: 0 = X (points, A-vertices), 1 = Y (lines, B-vertices).
    """
    k = len(S)
    n = 2 * m + 2 * k
    E = {_key(u, v) for u, v in edges}
    side = [0] * m + [1] * m + [0] * k + [1] * k
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.add(_key(m + L, x))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.add(_key(Q, b))
    return n, E, side


def _best_arc_base(d, rng, deadline):
    """Largest arc-extended base over prime powers q with q + 1 <= d."""
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        S = []
        if s >= 1:
            S = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(S) and _loads_ok(cs, s, m, point_lines, line_points):
                S = cs
        if not _loads_ok(S, s, m, point_lines, line_points):
            S = []
        n, E, side = _arc_base(m, edges, point_lines, line_points, S)
        if best is None or n > best[0]:
            best = (n, E, side)
    return best


def _augment(n, E, side, d, D, deadline, rng):
    """Greedy, oracle-checked addition of new vertices to a graph with spare capacity.

    A new vertex on side s is joined to opposite-side vertices with spare degree, chosen by
    greedy set cover so that all same-side vertices lie at distance 2. The candidate is kept
    only if lib.is_valid(n+1, ...) holds. Returns (n, edge set, side list).
    """
    E = set(E)
    side = list(side)
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    while time.monotonic() < deadline:
        s = rng.randrange(2)
        pool = [v for v in range(n) if side[v] == 1 - s and len(adj[v]) < d]
        if not pool:
            s = 1 - s
            pool = [v for v in range(n) if side[v] == 1 - s and len(adj[v]) < d]
            if not pool:
                break
        target = {v for v in range(n) if side[v] == s}
        rng.shuffle(pool)
        chosen = []
        covered = set()
        while len(chosen) < d and not target <= covered:
            best_y, best_gain = None, 0
            for y in pool:
                gain = len(adj[y] - covered)
                if gain > best_gain:
                    best_y, best_gain = y, gain
            if best_y is None:
                break
            chosen.append(best_y)
            covered |= adj[best_y]
            pool.remove(best_y)
        if not target <= covered:
            continue
        x = n
        E2 = E.union(_key(x, y) for y in chosen)
        if lib.is_valid(n + 1, list(E2), d, D):
            E = E2
            adj.append(set(chosen))
            for y in chosen:
                adj[y].add(x)
            side.append(s)
            n += 1
    return n, E, side


def _saturate(n, E, side, d, rng):
    """Add X-Y edges between vertices with spare degree; returns (n, sorted edge list)."""
    E = set(E)
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    X = [v for v in range(n) if side[v] == 0 and deg[v] < d]
    Y = [v for v in range(n) if side[v] == 1 and deg[v] < d]
    pairs = [(x, y) for x in X for y in Y]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d:
            continue
        k = _key(x, y)
        if k in E:
            continue
        E.add(k)
        deg[x] += 1
        deg[y] += 1
    return n, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.7 * time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best_e = list(best_e)

    if D >= 3:
        base = _best_arc_base(d, rng, start + 0.2 * (deadline - start))
        if base is not None:
            n0, E0, side0 = base
            cands = [_saturate(n0, E0, side0, d, rng)]
            n1, E1, side1 = _augment(n0, E0, side0, d, D, deadline, rng)
            cands.append(_saturate(n1, E1, side1, d, rng))
            for n_c, e_c in cands:
                if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
                    best_n, best_e = n_c, e_c

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
        best_e = list(best_e)
    return best_n, best_e
