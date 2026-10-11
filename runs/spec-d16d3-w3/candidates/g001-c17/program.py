"""Projective-plane arc extensions for diameter 3, plus a new degree-preserving
rewiring repair that inserts vertex pairs into an existing valid graph.

Repair idea: take a valid bipartite graph and pick d edges (x_i, y_i) with
pairwise distinct endpoints. Add a new X-vertex v and a new Y-vertex w, replace
each (x_i, y_i) by (x_i, w) and (v, y_i). Every old degree is preserved and
v, w have degree d. Then anneal with double-edge swaps across the bipartition
(degrees stay fixed) to minimise lib.bad_pairs. A zero cost gives a valid
graph with two more vertices.
"""
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base and arc extensions (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """Every line holds <= s points of S, and every point lies on <= s lines indexed by S."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG incidence plus a new A-vertex (clone of point) and B-vertex (clone of line) per element of S."""
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
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
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
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Helpers: bipartition and saturation (adding edges never increases diameter).
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Two-colouring of a bipartite graph given by an edge list."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    deg = [0] * n
    existing = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        existing.add((min(u, v), max(u, v)))
    color = _two_color(n, edges)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# New: degree-preserving rewiring repair that inserts one X/Y vertex pair.
# ----------------------------------------------------------------------------

def _insert_pair(n, edges, d, D, deadline, rng):
    """Try to add one X-vertex and one Y-vertex by rewiring; returns (n+2, edges) or None.

    Degrees of old vertices are preserved by the initial rewiring and by every
    double-edge swap, so max degree stays <= d and the graph stays bipartite.
    """
    color = _two_color(n, edges)
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]  # (x, y) pairs
    idx = list(range(len(E)))
    rng.shuffle(idx)
    usedX, usedY, pick = set(), set(), []
    for i in idx:
        x, y = E[i]
        if x in usedX or y in usedY:
            continue
        usedX.add(x)
        usedY.add(y)
        pick.append(i)
        if len(pick) == d:
            break
    if len(pick) < d:
        return None

    v, w = n, n + 1  # v on X side (colour 0), w on Y side (colour 1)
    pickset = set(pick)
    newE = [e for i, e in enumerate(E) if i not in pickset]
    for i in pick:
        x, y = E[i]
        newE.append((x, w))
        newE.append((v, y))
    N = n + 2

    cost = lib.bad_pairs(N, newE, D)
    edgeset = set(newE)
    T0 = 1.5
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = T0 * (0.02 ** ((now - t0) / span))
        i = rng.randrange(len(newE))
        j = rng.randrange(len(newE))
        if i == j:
            continue
        a, b = newE[i]
        c, e = newE[j]
        if a == c or b == e:
            continue
        if (a, e) in edgeset or (c, b) in edgeset:
            continue
        newE[i] = (a, e)
        newE[j] = (c, b)
        c2 = lib.bad_pairs(N, newE, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            edgeset.discard((a, b))
            edgeset.discard((c, e))
            edgeset.add((a, e))
            edgeset.add((c, b))
            cost = c2
        else:
            newE[i] = (a, b)
            newE[j] = (c, e)
    return N, newE


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if best_n >= lib.moore_bound(d, D):
        return best_n, best_e

    if D >= 3:
        cands = []
        pg = _best_pg(d)
        if pg is not None:
            cands.append(pg)
        arcs = _arc_extensions(d, start + 0.25 * time_limit,
                               random.Random(seed * 7919 + d))
        cands.extend(arcs)
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands[:4]:
            for e in (e_c, _saturate_edges(n_c, e_c, d, rng)):
                if n_c > best_n and lib.is_valid(n_c, e, d, D):
                    best_n, best_e = n_c, e

        # Repair stage: insert vertex pairs by degree-preserving rewiring.
        n_cur, e_cur = best_n, best_e
        while time.monotonic() < deadline and n_cur < lib.moore_bound(d, D):
            res = _insert_pair(n_cur, e_cur, d, D, deadline, rng)
            if res is None:
                break
            n_new, e_new = res
            if not lib.is_valid(n_new, e_new, d, D):
                break
            n_cur, e_cur = n_new, e_new
            best_n, best_e = n_cur, e_cur

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
