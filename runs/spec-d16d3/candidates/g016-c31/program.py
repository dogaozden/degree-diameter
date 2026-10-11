"""Arc-extended projective plane graphs (diameter 3), plus a repair search for D = 3.

Construction: start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
Each old vertex has degree q+1, so with d >= q+1 it has spare capacity s = d - q - 1.
Choose a point set S whose lines each hold at most s points of S (and, by duality, whose
points each lie on at most s lines indexed by S). For each P in S add an A-vertex joined to the
q+1 lines through P; for each j in S add a B-vertex joined to the q+1 points on line j.
Diameter stays 3 and the order is 2(q^2+q+1) + 2|S|. For d = 16 the conic/oval (|S| = 14,
q = 13) gives 394.

Bold attempt for D = 3: after building the best arc graph, run a simulated-annealing repair
search. It inserts one extra A-type and one extra B-type vertex, fills their spare degree, and
then performs degree-preserving edge swaps and relocations (keeping the bipartition) to drive
lib.bad_pairs to zero. A zero-cost state is re-verified with lib.is_valid before use. If the
search fails, the arc construction (or K_{d,d}) is returned, so every case still yields a
valid graph.

Only one attempt is made per call and the search is budgeted to a fraction of time_limit.
"""
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
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
    """Conic (plus nucleus for even q) as an index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A-vertex per element of S (joined to lines through it)
    and a new B-vertex per element of S (joined to points on that line)."""
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
    """Return a list of (n, edges) arc-extended graphs, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
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
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Repair search for D = 3: insert extra vertices and anneal toward zero bad pairs.
# ----------------------------------------------------------------------------

def _colors(n, edges):
    """Bipartition colours (0/1) of a bipartite graph by BFS."""
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


def _propose(adj, color, n, d, rng):
    """Propose a degree-preserving (or degree-respecting) move as a list of (is_add, a, b) ops."""
    r = rng.random()
    if r < 0.45:
        # Double edge swap inside one colour class.
        a = rng.randrange(n)
        a2 = rng.randrange(n)
        if a == a2 or color[a] != color[a2] or not adj[a] or not adj[a2]:
            return None
        b = rng.choice(tuple(adj[a]))
        b2 = rng.choice(tuple(adj[a2]))
        if b == b2 or b2 in adj[a] or b in adj[a2]:
            return None
        return [(False, a, b), (False, a2, b2), (True, a, b2), (True, a2, b)]
    if r < 0.7:
        # Relocate one endpoint of an edge to another vertex of the same colour as the old endpoint.
        x = rng.randrange(n)
        if not adj[x]:
            return None
        y = rng.choice(tuple(adj[x]))
        for _ in range(30):
            y2 = rng.randrange(n)
            if y2 != y and color[y2] == color[y] and y2 not in adj[x] and len(adj[y2]) < d:
                return [(False, x, y), (True, x, y2)]
        return None
    # Fill: add an edge between spare-degree vertices of opposite colour.
    x = rng.randrange(n)
    if len(adj[x]) >= d:
        return None
    for _ in range(30):
        y = rng.randrange(n)
        if color[y] != color[x] and len(adj[y]) < d and y not in adj[x]:
            return [(True, x, y)]
    return None


def _apply(adj, ops):
    for is_add, a, b in ops:
        if is_add:
            adj[a].add(b)
            adj[b].add(a)
        else:
            adj[a].discard(b)
            adj[b].discard(a)


def _undo(adj, ops):
    for is_add, a, b in reversed(ops):
        if is_add:
            adj[a].discard(b)
            adj[b].discard(a)
        else:
            adj[a].add(b)
            adj[b].add(a)


def _repair(n0, E0, d, D, deadline, rng):
    """Insert one A-type and one B-type vertex into (n0, E0) and anneal until diameter D holds.
    Returns (n, edges) on success, else None."""
    n = n0 + 2
    color = _colors(n0, E0) + [0, 1]
    adj = [set() for _ in range(n)]
    for u, v in E0:
        adj[u].add(v)
        adj[v].add(u)

    # Greedy initial fill of the two new vertices.
    for x in (n0, n0 + 1):
        cands = [y for y in range(n) if color[y] != color[x] and len(adj[y]) < d and y not in adj[x]]
        rng.shuffle(cands)
        for y in cands:
            if len(adj[x]) >= d:
                break
            if len(adj[y]) < d:
                adj[x].add(y)
                adj[y].add(x)

    def edges_of():
        return [(u, v) for u in range(n) for v in adj[u] if u < v]

    cur = lib.bad_pairs(n, edges_of(), D)
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t_start) / span
        T = max(0.15, 1.5 * (1.0 - frac))
        ops = _propose(adj, color, n, d, rng)
        if ops is None:
            continue
        _apply(adj, ops)
        new = lib.bad_pairs(n, edges_of(), D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            _undo(adj, ops)

    if cur == 0:
        E = edges_of()
        if lib.is_valid(n, E, d, D):
            return n, E
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

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    # Arc-extended projective plane graphs have diameter 3, so they are valid for D >= 3.
    if D >= 3 and d >= 2:
        try:
            cands = _arc_candidates(d, start + 0.25 * time_limit, random.Random(seed * 7919 + d))
        except Exception:
            cands = []
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
                best_n, best_E = n_c, e_c
                break

    # Bold attempt for D = 3: repair search that tries to add vertices beyond the arc construction.
    if D == 3 and d >= 2:
        moore = 2 * (1 + (d - 1) + (d - 1) ** 2)
        if best_n < moore and time.monotonic() < deadline:
            try:
                res = _repair(best_n, best_E, d, D, deadline, rng)
            except Exception:
                res = None
            if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
                best_n, best_E = res

    if not lib.is_valid(best_n, best_E, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_E
