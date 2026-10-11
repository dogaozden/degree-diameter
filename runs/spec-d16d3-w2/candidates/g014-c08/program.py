"""Arc-extended projective plane graphs (D = 3) with a cover-star repair search.

New in this version: _cover_star, a greedy set-cover helper. A new vertex x on
side sx needs every vertex on side sx within distance 2, so its neighbourhood N
(on the opposite side, with spare degree) must satisfy N(N) covering side sx.
_cover_star finds such an N greedily, and _repair uses it to add vertices and to
remove-and-refill. Every stored state is checked with lib.is_valid.
"""
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


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


def _conic_set(q, index):
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(S, m, edges, point_lines, line_points):
    """Points 0..m-1 (side 0), lines m..2m-1 (side 1), A vertices (side 0), B vertices (side 1)."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        for L in point_lines[P]:
            E.append((2 * m + t, m + L))
    for t, j in enumerate(S):
        for Q in line_points[j]:
            E.append((Q, 2 * m + k + t))
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _candidates(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index = _pg_data(q)
        S = []
        if s >= 1:
            S = _greedy_arc(m, s, pl, lp, rng, 30, deadline)
        if s >= 2:
            cs = _conic_set(q, index)
            if _loads_ok(cs, s, m, pl, lp) and len(cs) > len(S):
                S = cs
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(S, m, edges, pl, lp))
    return out


# ----------------------------------------------------------------------------
# Adjacency-set helpers.
# ----------------------------------------------------------------------------

def _to_adj(n, E, side):
    adj = {v: set() for v in range(n)}
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    return adj, {v: side[v] for v in range(n)}


def _graph_of(adj):
    return [(u, v) for u in adj for v in adj[u] if u < v]


def _valid(adj, d, D):
    n, E = lib.relabel(_graph_of(adj))
    return n > 0 and lib.is_valid(n, E, d, D)


# ----------------------------------------------------------------------------
# NEW helper: cover-star.
#
# A new vertex x on side sx joins N, a set of spare vertices on side 1-sx.
# Every vertex on side sx must lie within distance 2 of x, so N(N) must cover
# all of side sx. Greedy max-coverage picks the neighbourhood, with random
# tie-breaking. Returns None if coverage fails.
# ----------------------------------------------------------------------------

def _cover_star(adj, side, sx, d, rng):
    uncovered = {v for v in adj if side[v] == sx}
    if not uncovered:
        return None
    cands = [u for u in adj if side[u] == 1 - sx and len(adj[u]) < d]
    rng.shuffle(cands)
    chosen = []
    while uncovered and len(chosen) < d:
        best_u, best_g = None, 0
        for u in cands:
            g = len(adj[u] & uncovered)
            if g > best_g:
                best_u, best_g = u, g
        if best_u is None:
            break
        chosen.append(best_u)
        uncovered -= adj[best_u]
        cands.remove(best_u)
    if uncovered or len(chosen) < 2:
        return None
    return chosen


# ----------------------------------------------------------------------------
# Repair search: remove-and-refill with cover-star moves. Every accepted state
# passes lib.is_valid. Returns (count, adj, side) for the best state seen.
# ----------------------------------------------------------------------------

def _repair(adj, side, d, D, deadline, rng):
    cur, cside = adj, side
    best = (len(adj), adj, side)
    while time.monotonic() < deadline:
        new = {u: set(s) for u, s in cur.items()}
        nside = dict(cside)
        if rng.random() < 0.5 and len(new) > 4:
            v = rng.choice(list(new))
            for u in new.pop(v):
                new[u].discard(v)
                if not new[u]:
                    del new[u]
                    del nside[u]
            del nside[v]
        for _ in range(6):
            sx = rng.randrange(2)
            nb = _cover_star(new, nside, sx, d, rng)
            if nb is None:
                continue
            x = max(new) + 1
            new[x] = set(nb)
            nside[x] = sx
            for u in nb:
                new[u].add(x)
        if len(new) < len(cur) and rng.random() > 0.05:
            continue
        if not _valid(new, d, D):
            continue
        cur, cside = new, nside
        if len(cur) > best[0]:
            best = (len(cur), cur, cside)
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is a safe fallback for D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    # Arc-extended projective plane graphs have diameter 3, so they are valid for D >= 3.
    cands = _candidates(d, start + 0.15 * time_limit, rng)
    if cands:
        cands.sort(key=lambda c: -c[0])
        n0, E0, side0 = cands[0]
        if n0 > best[0] and lib.is_valid(n0, E0, d, D):
            best = (n0, E0)
        if lib.moore_bound(d, D) > n0 and time.monotonic() < deadline:
            adj, side = _to_adj(n0, E0, side0)
            _, adj_b, _ = _repair(adj, side, d, D, deadline, rng)
            n, E2 = lib.relabel(_graph_of(adj_b))
            if n > best[0] and lib.is_valid(n, E2, d, D):
                best = (n, E2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
