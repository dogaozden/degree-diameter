import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Popcount helper (int.bit_count needs Python 3.10+).
# ----------------------------------------------------------------------------

_pc = (lambda x: x.bit_count()) if hasattr(int, "bit_count") else (lambda x: bin(x).count("1"))


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare capacity s = d - q - 1. Pick a point set S whose
# every line carries <= s points of S. For each P in S add an A-vertex joined
# to the q+1 lines through P; for each j in S add a B-vertex joined to the q+1
# points on line j. Diameter stays 3.
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


def _arc_graph(m, edges, point_lines, S, line_points):
    """Old PG incidence plus a new A and a new B vertex for each element of S."""
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
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Graph helpers.
# ----------------------------------------------------------------------------

def _adj_lists(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
    """2-colouring of a bipartite graph given by adjacency lists."""
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


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (bitmask balls)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - _pc(r) for r in reach) // 2


# ----------------------------------------------------------------------------
# Repair search: add ONE vertex to a valid graph by simulated annealing.
#
# State: a bipartite graph on n+1 vertices (the new vertex starts isolated)
# with max degree <= d held as a hard constraint. Moves:
#   * degree-preserving 2-switches (keeps every degree, so it reshapes the
#     graph without breaking the degree cap),
#   * adding a cross edge between two vertices that both have spare degree,
#   * removing a random cross edge.
# Cost = number of vertex pairs farther apart than D. Zero means valid.
# This goes beyond the algebraic constructions: it rewires existing edges
# to make room for the extra vertex's coverage.
# ----------------------------------------------------------------------------

def _repair(n, edges, col, d, D, deadline, rng, newside):
    """Try to add one vertex; return (n+1, edges, side) on success, else None."""
    N = n + 1
    side = list(col) + [newside]
    adj = [set() for _ in range(N)]
    E = []
    pos = {}

    def add_e(u, v):
        a, b = (u, v) if side[u] == 0 else (v, u)
        pos[(a, b)] = len(E)
        E.append((a, b))
        adj[a].add(b)
        adj[b].add(a)

    def rem_e(a, b):
        i = pos.pop((a, b))
        last = E.pop()
        if i < len(E):
            E[i] = last
            pos[last] = i
        adj[a].discard(b)
        adj[b].discard(a)

    for u, v in edges:
        add_e(u, v)
    if len(pos) != len(edges):
        return None

    cost = _bad(N, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 1.5, 0.05

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        r = rng.random()

        if r < 0.5 and len(E) >= 2:
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            a, b = E[i]
            c, e2 = E[j]
            if a == c or b == e2 or e2 in adj[a] or b in adj[c]:
                continue
            rem_e(a, b)
            rem_e(c, e2)
            add_e(a, e2)
            add_e(c, b)
            c2 = _bad(N, adj, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                rem_e(a, e2)
                rem_e(c, b)
                add_e(a, b)
                add_e(c, e2)

        elif r < 0.8:
            us = [v for v in range(N) if side[v] == 0 and len(adj[v]) < d]
            vs = [v for v in range(N) if side[v] == 1 and len(adj[v]) < d]
            if not us or not vs:
                continue
            u = rng.choice(us)
            v = rng.choice(vs)
            if v in adj[u]:
                continue
            add_e(u, v)
            c2 = _bad(N, adj, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                rem_e(u, v)

        else:
            if not E:
                continue
            a, b = E[rng.randrange(len(E))]
            rem_e(a, b)
            c2 = _bad(N, adj, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                add_e(a, b)

    return N, list(E), side


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Algebraic start: arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, start + 0.15 * time_limit, random.Random(seed * 7919 + d))
        for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
            consider(n_c, e_c)

    # Bold stage: grow the best graph one vertex at a time by annealed repair.
    if D >= 3 and best[0] >= 2:
        n_cur, e_cur = best
        col = _bipartition(n_cur, _adj_lists(n_cur, e_cur))
        rng = random.Random(seed * 1009 + d)
        while True:
            remaining = hard - time.monotonic()
            if remaining < 0.3:
                break
            res = _repair(n_cur, e_cur, col, d, D,
                          time.monotonic() + 0.5 * remaining, rng, rng.randrange(2))
            if res is None:
                continue
            n_new, e_new, side_new = res
            if not lib.is_valid(n_new, e_new, d, D):
                break
            n_cur, e_cur, col = n_new, e_new, side_new
            best = (n_cur, e_cur)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
