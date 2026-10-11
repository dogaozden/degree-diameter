"""Clone-extension family for diameter 3 (bipartite).

Base: incidence graph of PG(2, q), q a prime power with q + 1 <= d, so each
vertex has spare capacity s = d - q - 1.

Extension: for a point set S, add one "A" vertex per point x in S, joined to
the q+1 lines through x. For a line set T, add one "B" vertex per line L in T,
joined to the q+1 points on L. The constraints are that every line contains at
most s points of S and every point lies on at most s lines of T.

Why diameter 3 holds: same-side pairs get a common neighbour (A_x and an old
point P share the line xP; A_x and A_y share the line xy), and cross-side
pairs are at distance 1 or 3. lib.is_valid still checks every output.

Limit of this family: for odd q, a set with at most two points per line has at
most q+1 points. For d = 16 (q = 13, s = 2), this caps |S| and |T| at 14, so the
family gives 2*183 + 14 + 14 = 394, which matches the record but does not beat it.
A bigger gain needs vertices that are not clones of points or lines.

Fallback: K_{d,d} (diameter 2) for D >= 2, which is valid for every case.
"""
import random
import time

import lib


def _pg(q):
    """Return (m, edges, point_lines, line_points, pts) for PG(2, q); points are 0..m-1, lines are m..2m-1."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points, pts


def _conic_start(q, pts, m, s, point_lines):
    """Conic (plus nucleus when q is even) as an initial point set; [] if it violates the load limit."""
    try:
        F = lib.GF(q)
    except ValueError:
        return []
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    load = [0] * m
    for P in S:
        for L in point_lines[P]:
            load[L] += 1
    return S if max(load) <= s else []


def _arc_search(m, s, point_lines, line_points, start, rng, deadline):
    """Local search for a point set where every line holds at most s chosen points.

    Moves: add a free point, or swap in a point whose single full line gives up one chosen point.
    Returns the largest set seen.
    """
    if s < 1:
        return []
    inS = [False] * m
    load = [0] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in point_lines[P]:
            load[L] += 1

    def drop(Q):
        inS[Q] = False
        S.remove(Q)
        for L in point_lines[Q]:
            load[L] -= 1

    for P in start:
        if not inS[P] and all(load[L] < s for L in point_lines[P]):
            add(P)
    order = list(range(m))
    rng.shuffle(order)
    for P in order:
        if not inS[P] and all(load[L] < s for L in point_lines[P]):
            add(P)
    best = list(S)

    while time.monotonic() < deadline:
        for _ in range(300):
            P = rng.randrange(m)
            if inS[P]:
                continue
            full = [L for L in point_lines[P] if load[L] >= s]
            if not full:
                add(P)
            elif len(full) == 1:
                L = full[0]
                cands = [Q for Q in line_points[L] if inS[Q]]
                drop(rng.choice(cands))
                add(P)
        if len(S) > len(best):
            best = list(S)
    return best


def _clone_graph(m, edges, point_lines, line_points, S, T):
    """Base incidence graph plus an A-vertex per point of S and a B-vertex per line of T."""
    n = 2 * m + len(S) + len(T)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    base_b = 2 * m + len(S)
    for t, L in enumerate(T):
        y = base_b + t
        for Q in line_points[L]:
            E.append((Q, y))
    return n, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1:
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

    if D >= 3:
        qs = [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)]
        qs = qs[:3]
        for idx, q in enumerate(qs):
            now = time.monotonic()
            if now >= deadline:
                break
            share = (deadline - now) / (len(qs) - idx)
            s = d - q - 1
            if s < 0:
                continue
            m, edges, point_lines, line_points, pts = _pg(q)
            if s == 0:
                consider(2 * m, edges)
                continue
            conic = _conic_start(q, pts, m, s, point_lines)
            half = share / 2.0
            S = _arc_search(m, s, point_lines, line_points, conic, rng,
                            time.monotonic() + half)
            T = _arc_search(m, s, line_points, point_lines, conic, rng,
                            time.monotonic() + half)
            n, e = _clone_graph(m, edges, point_lines, line_points, S, T)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
