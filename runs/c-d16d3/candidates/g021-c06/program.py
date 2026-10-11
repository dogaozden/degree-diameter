import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S
# that is an arc (each line holds <= s points of S, each point lies on <= s
# lines indexed by S). For each P in S add a new A-vertex on the lines through
# P, and for each j in S add a new B-vertex on the points of line j.
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A-vertex per point of S and a new B-vertex per line of S."""
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


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, _ = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# New helper: covering insertion and removal/reinsertion local search.
#
# Adding a vertex x on side c is valid (diameter stays <= 3) iff its neighbour
# set N, all of the opposite side with spare degree, satisfies
#     union over n in N of ball2(n) = all vertices.
# Adding x never lengthens an existing distance, so validity is preserved.
# The local search deletes 1-3 random vertices, greedily re-inserts as many
# vertices as possible by set cover, and accepts the result when the order
# does not drop and the diameter is still <= 3. This walks across plateaus
# of equal-order valid graphs and records the largest order seen.
# ----------------------------------------------------------------------------

def _adj_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _closed_masks(n, adj):
    """Bitmask of the closed neighbourhood N[v] for each v."""
    out = []
    for v in range(n):
        m = 1 << v
        for u in adj[v]:
            m |= 1 << u
        out.append(m)
    return out


def _ball2(n, adj, r1):
    """Bitmask of vertices within distance 2 of each v."""
    r2 = [0] * n
    for v in range(n):
        m = r1[v]
        for u in adj[v]:
            m |= r1[u]
        r2[v] = m
    return r2


def _diam3(n, adj):
    """True if the graph is connected with diameter <= 3."""
    if n <= 1:
        return True
    r1 = _closed_masks(n, adj)
    r2 = _ball2(n, adj, r1)
    full = (1 << n) - 1
    for v in range(n):
        m = r2[v]
        for u in adj[v]:
            m |= r2[u]
        if m != full:
            return False
    return True


def _color(n, adj):
    """BFS 2-colouring; assumes the graph is bipartite."""
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


def _try_insert(n, adj, color, d, rng, trials):
    """Find (side, N) for a new vertex that keeps diameter 3, or None."""
    full = (1 << n) - 1
    r1 = _closed_masks(n, adj)
    r2 = _ball2(n, adj, r1)
    sides = [0, 1]
    rng.shuffle(sides)
    for side in sides:
        cands0 = [v for v in range(n) if color[v] == 1 - side and len(adj[v]) < d]
        if not cands0:
            continue
        for _ in range(trials):
            pool = cands0[:]
            rng.shuffle(pool)
            covered = 0
            N = []
            while covered != full and len(N) < d and pool:
                bi = -1
                bg = 0
                for i, c in enumerate(pool):
                    g = (r2[c] & ~covered).bit_count()
                    if g > bg:
                        bg = g
                        bi = i
                if bi < 0:
                    break
                covered |= r2[pool[bi]]
                N.append(pool[bi])
                pool[bi] = pool[-1]
                pool.pop()
            if covered == full:
                return side, N
    return None


def _apply(adj, color, side, N):
    x = len(adj)
    adj.append(set(N))
    color.append(side)
    for c in N:
        adj[c].add(x)


def _local_search(n0, edges, d, deadline, rng):
    """Remove/reinsert local search; returns the largest valid (n, edges) found."""
    adj = _adj_sets(n0, edges)
    col = _color(n0, adj)
    best_n, best_edges = n0, list(edges)
    cur_n = n0
    while time.monotonic() < deadline:
        k = 1 if rng.random() < 0.7 else rng.randint(2, 3)
        removed = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in removed]
        idx = {v: i for i, v in enumerate(keep)}
        nadj = [set(idx[u] for u in adj[v] if u not in removed) for v in keep]
        ncol = [col[v] for v in keep]
        for _ in range(4):
            r = _try_insert(len(nadj), nadj, ncol, d, rng, trials=4)
            if r is None:
                break
            _apply(nadj, ncol, r[0], r[1])
        m = len(nadj)
        if m >= cur_n and _diam3(m, nadj):
            adj, col, cur_n = nadj, ncol, m
            if m > best_n:
                best_n = m
                best_edges = [(u, v) for u in range(m) for v in nadj[u] if u < v]
    return best_n, best_edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    # D >= 3: arc-extended projective plane graphs (diameter 3).
    cands = _arc_extensions(d, deadline, random.Random(seed * 7919 + d))
    for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
        if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)
            break

    # Covering-insertion local search from the best arc graph.
    adj0 = _adj_sets(best[0], best[1])
    has_spare = any(len(a) < d for a in adj0)
    if has_spare and time.monotonic() < deadline:
        n_r, e_r = _local_search(best[0], best[1], d, deadline, rng)
        if n_r > best[0] and lib.is_valid(n_r, e_r, d, D):
            best = (n_r, e_r)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
