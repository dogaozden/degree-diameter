import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base family: incidence graph of PG(2, q), extended by a conic "arc".
#
# Points and lines of PG(2, q) are both indexed by the same projective vectors.
# A conic S (plus the nucleus when q is even) is an arc, so no three of its
# points are collinear and no three of its lines are concurrent. For each
# element of S we add an A-vertex on the point side (joined to its q+1 lines)
# and a B-vertex on the line side (joined to its q+1 points). Every old vertex
# gains at most 2 new edges, which fits when d - q - 1 >= 2.
#
# Limitation: with spare capacity 2 this arc family is capped at q+1 extra
# A/B pairs (an arc has at most q+2 points), so it stops near 394 for d=16.
# The new step here is a cover-based augmentation pass that runs on top of
# the arc graph and uses any leftover spare degree, not just the arc vertices.
# ----------------------------------------------------------------------------

def _conic(q, pts, F):
    """Point-index set of a conic (plus nucleus for even q): an arc."""
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _pg_arc_graph(q):
    """PG(2, q) incidence graph plus A and B vertices for a conic arc. Returns (n, edges)."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    S = _conic(q, pts, F)
    k = len(S)

    point_lines = [[] for _ in range(m)]   # line indices through each point
    line_points = [[] for _ in range(m)]   # point indices on each line
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)

    E = list(edges)
    for t, P in enumerate(S):              # A-vertex for each arc point
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):              # B-vertex for each arc line (same index set)
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return 2 * m + 2 * k, E


# ----------------------------------------------------------------------------
# Cover-based augmentation: add a vertex whose neighbourhood, among vertices
# with spare degree, lies on the opposite colour class and covers every vertex
# within distance D-1 of it. Adding a vertex never breaks existing distances.
# ----------------------------------------------------------------------------

def _colors(n, adj):
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


def _balls(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _cover_grow(n, edges, d, D, deadline, rng):
    """Repeatedly add cover vertices while possible (before the deadline)."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _colors(n, adj)

    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            pool = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not pool:
                continue
            rng.shuffle(pool)
            covered = 0
            chosen = []
            while covered != full and len(chosen) < d and pool:
                best_i, best_g = -1, 0
                for i, s in enumerate(pool):
                    g = (ball[s] & ~covered).bit_count()
                    if g > best_g:
                        best_i, best_g = i, g
                if best_i < 0:
                    break
                s = pool.pop(best_i)
                chosen.append(s)
                covered |= ball[s]
            if covered == full and chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Top-level construction.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.6 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2 or D >= 4:
        # D = 2 is optimal with K_{d,d}. Other D >= 4 are not handled by this
        # program, so they keep the fallback.
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # D == 3: incidence graphs of PG(2, q) with q + 1 <= d, each augmented
    # by a conic arc (if spare allows) and then by cover growth.
    qs = [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)]
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        q_deadline = now + share
        s = d - q - 1

        if s == 0:
            n, e = lib.projective_plane_incidence(q)
            consider(n, e)
            continue

        n, e = _pg_arc_graph(q)
        if s >= 2 or lib.is_valid(n, e, d, D):
            consider(n, e)
            n2, e2 = _cover_grow(n, e, d, D, q_deadline, rng)
            consider(n2, e2)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
