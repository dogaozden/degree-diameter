"""Arc-extended projective plane graphs with coverage-based vertex insertion.

Base: incidence graph of PG(2, q) plus, for each point P of an arc S, a new
vertex A_P joined to the q+1 lines through P, and for each j in S a new vertex
B_j joined to the q+1 points on line j. Spare degree (d - q - 1) limits how many
times each old vertex may be used.

New idea (coverage insertion): a new vertex X joined to a set N keeps diameter
<= D iff every existing vertex lies within distance D-1 of some vertex of N.
Adding vertices or edges never breaks existing pairs, so each insertion is
checked with bitmask ball unions and a greedy set cover over spare-degree
vertices of the opposite side. When insertion stalls, random edges between
spare vertices are added, since they only enlarge balls.
"""
import random
import time

import lib


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


def _find_arc(q, s, m, point_lines, line_points, index, rng):
    """Find a point set S with all loads <= s: a conic (plus nucleus for even q) or randomized greedy."""
    if s <= 0:
        return []
    F = lib.GF(q)
    conic = [index[(1, t, F.mul(t, t))] for t in range(q)]
    conic.append(index[(0, 0, 1)])
    if q % 2 == 0:
        conic.append(index[(0, 1, 0)])
    best = conic if _loads_ok(conic, s, m, point_lines, line_points) else []
    order = list(range(m))
    for _ in range(30):
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


def _arc_base(q, d, rng):
    """Return (n, adj, side) for the arc-extended PG(2, q) graph with max degree d, or None."""
    s = d - q - 1
    if s < 0:
        return None
    m2, pg_edges = lib.projective_plane_incidence(q)
    m = m2 // 2
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in pg_edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    S = _find_arc(q, s, m, point_lines, line_points, index, rng)
    if not _loads_ok(S, s, m, point_lines, line_points):
        return None
    k = len(S)
    n = 2 * m + 2 * k
    adj = [set() for _ in range(n)]

    def link(u, v):
        adj[u].add(v)
        adj[v].add(u)

    for u, v in pg_edges:
        link(u, v)
    for t, P in enumerate(S):
        for L in point_lines[P]:
            link(2 * m + t, m + L)
    for t, j in enumerate(S):
        for Q in line_points[j]:
            link(Q, 2 * m + k + t)
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, adj, side


def _closed_balls(adj, R):
    """Bitmask per vertex of all vertices within distance R (R >= 1)."""
    n = len(adj)
    cur = [1 << v for v in range(n)]
    for u in range(n):
        for v in adj[u]:
            cur[u] |= 1 << v
    for _ in range(R - 1):
        nxt = []
        for v in range(n):
            acc = cur[v]
            for u in adj[v]:
                acc |= cur[u]
            nxt.append(acc)
        cur = nxt
    return cur


def _cover(adj, side, d, balls, full, opp, rng):
    """Greedy set cover: pick <= d spare vertices on side opp whose balls cover everything."""
    cands = [v for v in range(len(adj)) if side[v] == opp and len(adj[v]) < d]
    covered = 0
    chosen = []
    while covered != full:
        if len(chosen) >= d or not cands:
            return None
        best_i = -1
        best_key = -1.0
        for i, v in enumerate(cands):
            g = (balls[v] & ~covered).bit_count()
            if g:
                key = g + rng.random()
                if key > best_key:
                    best_key = key
                    best_i = i
        if best_i < 0:
            return None
        v = cands.pop(best_i)
        chosen.append(v)
        covered |= balls[v]
    return chosen


def _edge_fill(adj, side, d, rng, tries):
    """Add random edges between spare vertices of opposite sides (only enlarges balls)."""
    for _ in range(tries):
        us = [v for v in range(len(adj)) if side[v] == 0 and len(adj[v]) < d]
        vs = [v for v in range(len(adj)) if side[v] == 1 and len(adj[v]) < d]
        if not us or not vs:
            return
        for _ in range(40):
            u = rng.choice(us)
            v = rng.choice(vs)
            if v not in adj[u]:
                adj[u].add(v)
                adj[v].add(u)
                break


def _augment(adj, side, d, D, deadline, rng):
    """Insert vertices by coverage while time remains; mutates adj and side."""
    R = max(1, D - 1)
    fails = 0
    while time.monotonic() < deadline:
        if all(len(adj[v]) >= d for v in range(len(adj))):
            break
        full = (1 << len(adj)) - 1
        balls = _closed_balls(adj, R)
        opp = rng.randrange(2)
        chosen = _cover(adj, side, d, balls, full, opp, rng)
        if chosen is not None:
            x = len(adj)
            adj.append(set())
            side.append(1 - opp)
            for u in chosen:
                adj[x].add(u)
                adj[u].add(x)
            fails = 0
            continue
        fails += 1
        if fails >= 4:
            _edge_fill(adj, side, d, rng, 2)
            fails = 0
    return len(adj)


def _edges(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D < 3 or d < 3:
        return fallback

    best_base = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        base = _arc_base(q, d, rng)
        if base is not None and (best_base is None or base[0] > best_base[0]):
            best_base = base
    if best_base is None:
        return fallback

    n, adj, side = best_base
    base_edges = _edges(adj)
    if not lib.is_valid(n, base_edges, d, D):
        return fallback
    best = (n, base_edges)

    _augment(adj, side, d, D, deadline, rng)
    E = _edges(adj)
    if len(adj) > n and lib.is_valid(len(adj), E, d, D):
        return len(adj), E
    return best
