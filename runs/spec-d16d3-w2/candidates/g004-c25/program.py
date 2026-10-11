"""Arc-extended projective plane incidence graphs with validated slot-probe augmentation.

Base: incidence graph of PG(2, q), diameter 3, degree q+1. With d >= q+1 each old vertex
has spare s = d - q - 1. Pick S (a point set with at most s points of S on every line and at
most s lines through S-points on every point, i.e. an s-arc in the dual sense). For each P in S
add an A-vertex on the pencil of P; for each j in S add a B-vertex on the points of line j.

New in this version: after the arc graph is built, a slot-probe augmentation tries to add
extra vertices. Each probe picks a side, greedily chooses up to d spare opposite-side
vertices that together reach every same-side vertex within distance 2, and keeps the
vertex only if lib.is_valid still passes. Saturation then adds spare X-Y edges. Every
candidate is validated, so the output is never invalid.

Note: for d=16, D=3, a single added vertex needs a full pencil (or dual blocking set) whose
lines all have spare capacity. In the 394-vertex graph that does not exist, so the probe is
expected to add nothing there. It is a safety-checked extension, not a proven improvement.
"""
import random
import time

import lib


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q); lines are indexed like points."""
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
    """Randomized greedy S with all loads <= s; returns the largest found."""
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
    """Old PG incidence plus a new A-vertex (on the pencil of P) and a new B-vertex (on line P) per P in S.

    Vertex layout: points 0..m-1 (side 0), lines m..2m-1 (side 1), A-vertices 2m..2m+k-1 (side 0),
    B-vertices 2m+k..2m+2k-1 (side 1).
    """
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
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _augment(n, E, side, d, D, deadline, rng, max_attempts):
    """Slot-probe augmentation: add vertices joined to a greedy cover of spare opposite-side vertices.

    A probe with side s adds w on side s, joined to spare vertices on the other side whose
    neighbourhoods cover all side-s vertices (so every side-s vertex is at distance 2 from w,
    every other-side vertex at distance <= 3). The vertex is kept only if lib.is_valid accepts.
    """
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    E = list(E)
    side = list(side)
    attempts = 0
    while attempts < max_attempts and time.monotonic() < deadline:
        attempts += 1
        s = rng.randrange(2)
        cand = [y for y in range(n) if side[y] != s and len(adj[y]) < d]
        if not cand:
            continue
        rng.shuffle(cand)
        uncovered = {v for v in range(n) if side[v] == s}
        chosen = []
        chosen_set = set()
        while uncovered and len(chosen) < d:
            best, bg = None, 0
            for y in cand:
                if y in chosen_set:
                    continue
                g = len(adj[y] & uncovered)
                if g > bg:
                    best, bg = y, g
            if best is None:
                break
            chosen.append(best)
            chosen_set.add(best)
            uncovered -= adj[best]
        if uncovered or not chosen:
            continue
        w = n
        new_edges = [(w, y) for y in chosen]
        E2 = E + new_edges
        n2 = n + 1
        side2 = side + [s]
        if lib.is_valid(n2, E2, d, D):
            n = n2
            E = E2
            side = side2
            adj.append(set(chosen))
            for y in chosen:
                adj[y].add(w)
    return n, E, side


def _saturate(n, E, side, d, rng):
    """Add X-Y edges (side 0 to side 1) while both endpoints have spare degree. Keeps bipartiteness."""
    Es = set()
    for u, v in E:
        Es.add((u, v) if u < v else (v, u))
    deg = [0] * n
    for u, v in Es:
        deg[u] += 1
        deg[v] += 1
    spare0 = [v for v in range(n) if side[v] == 0 and deg[v] < d]
    spare1 = [v for v in range(n) if side[v] == 1 and deg[v] < d]
    pairs = [(x, y) for x in spare0 for y in spare1]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d:
            continue
        key = (x, y) if x < y else (y, x)
        if key in Es:
            continue
        Es.add(key)
        deg[x] += 1
        deg[y] += 1
    return n, sorted(Es)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D < 3:
        return best

    # Pick the largest arc-extended PG(2,q) candidate over prime powers q <= d-1.
    cand = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
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
        n_c, E_c, side_c = _arc_graph(m, edges, point_lines, line_points, S)
        if cand is None or n_c > cand[0]:
            cand = (n_c, E_c, side_c)

    if cand is not None:
        n_c, E_c, side_c = cand
        n_c, E_c, side_c = _augment(n_c, E_c, side_c, d, D, deadline, rng, max_attempts=4000)
        n_c, E_c = _saturate(n_c, E_c, side_c, d, rng)
        if n_c > best[0] and lib.is_valid(n_c, E_c, d, D):
            best = (n_c, E_c)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
