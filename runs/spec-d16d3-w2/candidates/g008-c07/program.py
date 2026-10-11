import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction: arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the point-line incidence graph of PG(2, q). Each old vertex has
# degree q+1, so it has spare capacity s = d - q - 1. Choose a point set S whose
# lines each hold at most s points of S. Each P in S gets a new X-vertex joined
# to the q+1 lines through P (a pencil, which covers every point within 2). Each
# j in S gets a new Y-vertex joined to the q+1 points on j. Then add every
# spare X-Y pair (this only shortens distances), so the graph stays bipartite
# with diameter <= 3.
#
# Search: from the best such graph, repeatedly remove a few edges to free spare
# degree, then greedily add new vertices whose neighbourhoods cover all
# same-side vertices within distance 2. Every candidate is checked with
# lib.is_valid, and the best valid graph is kept.
#
# Side convention: side 0 = X (old points, new X-vertices), side 1 = Y (old lines,
# new Y-vertices). Edges always join side 0 to side 1.
# ----------------------------------------------------------------------------


def _pg(q):
    """Return (m, edges, point_lines, line_points, pts) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pts = lib.projective_points(q)
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points, pts


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


def _saturate(n, edges, side, d, rng):
    """Add X-Y edges between vertices with spare degree (never increases a distance)."""
    E = set()
    for u, v in edges:
        E.add((u, v) if u < v else (v, u))
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
        key = (x, y) if x < y else (y, x)
        if key in E:
            continue
        E.add(key)
        deg[x] += 1
        deg[y] += 1
    return sorted(E)


def _arc_base(q, d, rng, deadline):
    """Build the arc-extended incidence graph for PG(2, q) with max degree d. Returns (n, edges, side) or None."""
    m, edges, point_lines, line_points, pts = _pg(q)
    index = {p: i for i, p in enumerate(pts)}
    s = d - q - 1
    if s < 0:
        return None
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
        return None
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        y = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, y))
    side = [0] * m + [1] * m + [0] * k + [1] * k
    E = _saturate(n, E, side, d, rng)
    return n, E, side


def _add_vertex(n, adj, deg, side, t, d, rng):
    """Greedy set cover: pick <= d opposite-side vertices with spare degree whose neighbourhoods
    cover all side-t vertices. Returns the chosen list, or None."""
    need = set(v for v in range(n) if side[v] == t)
    cand = [y for y in range(n) if side[y] != t and deg[y] < d]
    rng.shuffle(cand)
    chosen = []
    while need and len(chosen) < d and cand:
        best_gain, best_y = 0, None
        for y in cand:
            g = len(adj[y] & need)
            if g > best_gain:
                best_gain, best_y = g, y
        if best_y is None:
            break
        chosen.append(best_y)
        need -= adj[best_y]
        cand.remove(best_y)
    if need or not chosen:
        return None
    return chosen


def _search(n, E, side, d, D, deadline, rng):
    """Local search: perturb by removing a few edges, then add vertices, keeping only valid growth."""
    best = (n, list(E), list(side))
    cur_n, cur_E, cur_side = n, list(E), list(side)
    while time.monotonic() < deadline:
        E2 = list(cur_E)
        for _ in range(rng.randrange(0, 4)):
            if E2:
                E2.pop(rng.randrange(len(E2)))
        n2 = cur_n
        side2 = list(cur_side)
        adj = [set() for _ in range(n2)]
        for u, v in E2:
            adj[u].add(v)
            adj[v].add(u)
        deg = [len(a) for a in adj]
        added = 0
        for _ in range(3):
            if time.monotonic() > deadline:
                break
            t = rng.randrange(2)
            ch = _add_vertex(n2, adj, deg, side2, t, d, rng)
            if ch is None:
                continue
            adj.append(set(ch))
            deg.append(len(ch))
            side2.append(t)
            for y in ch:
                adj[y].add(n2)
                deg[y] += 1
                E2.append((y, n2))
            n2 += 1
            added += 1
        if added and n2 > cur_n and lib.is_valid(n2, E2, d, D):
            cur_n, cur_E, cur_side = n2, E2, side2
            if cur_n > best[0]:
                best = (cur_n, list(cur_E), list(cur_side))
    return best[0], best[1]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.7 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])
    if d == 1:
        return 2, [(0, 1)]

    # Safe fallbacks.
    if d == 2:
        n = 2 * D
        fb = (n, [(i, (i + 1) % n) for i in range(n)])  # even cycle C_{2D}: diameter D
    else:
        fb = lib.haar_graph(d, range(d))  # K_{d,d}: diameter 2
    if not lib.is_valid(fb[0], fb[1], d, D):
        fb = lib.haar_graph(d, range(d))
    best = fb

    if d == 2 or D < 3:
        return best

    # Arc-extended projective plane graphs (diameter 3, valid for all D >= 3).
    cands = []
    for q in range(min(d - 1, 23), 1, -1):
        if time.monotonic() > deadline:
            break
        if not lib.is_prime_power(q):
            continue
        res = _arc_base(q, d, rng, deadline)
        if res is None:
            continue
        n_c, e_c, side_c = res
        if lib.is_valid(n_c, e_c, d, D):
            cands.append((n_c, e_c, side_c))
    if not cands:
        return best

    cands.sort(key=lambda t: -t[0])
    n0, e0, s0 = cands[0]
    if n0 > best[0]:
        best = (n0, e0)

    # Bold step: local search that grows the best arc graph by adding vertices.
    n1, e1 = _search(n0, e0, s0, d, D, deadline, rng)
    if n1 > best[0] and lib.is_valid(n1, e1, d, D):
        best = (n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
