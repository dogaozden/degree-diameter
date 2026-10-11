import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane data and arc sets (loads <= s on both sides).
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


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG incidence plus, per S element t: an A-vertex x=2m+t (on lines through S[t])
    and a B-vertex y=2m+k+t (joined to points on line S[t])."""
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


# ----------------------------------------------------------------------------
# NEW: pencil-cover growth.
#
# A new vertex v is exact-valid for diameter D iff the union of the (D-1)-balls
# of its neighbours covers the whole graph. Here the candidate neighbour sets
# are whole pencils of the projective plane: the points of a line (for a new
# B-vertex) or the lines through a point (for a new A-vertex). Each pencil
# member uses its primary vertex, or its arc-companion vertex (x for a point,
# y for a line) when the primary one is saturated. Accepted candidates are
# checked by bitmask coverage, so every growth step is exact.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _choose(kind, mem, prefer_secondary, m, pt_to_x, line_to_y, deg, d):
    """Pick one neighbour per pencil member, or None if some member is saturated."""
    out = []
    for x in mem:
        if kind == 'P':
            pri, sec = x, pt_to_x.get(x)
        else:
            pri, sec = m + x, line_to_y.get(x)
        options = [sec, pri] if prefer_secondary else [pri, sec]
        pick = None
        for o in options:
            if o is not None and deg[o] < d:
                pick = o
                break
        if pick is None:
            return None
        out.append(pick)
    return out


def _pencil_grow(n, edges, m, S, point_lines, line_points, d, D, deadline, rng):
    k = len(S)
    pt_to_x = {S[t]: 2 * m + t for t in range(k)}
    line_to_y = {S[t]: 2 * m + k + t for t in range(k)}
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = [0 if (v < m or 2 * m <= v < 2 * m + k) else 1 for v in range(n)]

    pencils = [('P', line_points[L]) for L in range(m)] + \
              [('L', point_lines[P]) for P in range(m)]
    if D - 1 < 1:
        return n, edges

    while time.monotonic() < deadline:
        balls = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        order = list(range(len(pencils)))
        rng.shuffle(order)
        added = False
        for idx in order:
            if time.monotonic() >= deadline:
                break
            kind, mem = pencils[idx]
            if len(mem) > d:
                continue
            for pref in (False, True):
                out = _choose(kind, mem, pref, m, pt_to_x, line_to_y, deg, d)
                if out is None:
                    continue
                if len({color[c] for c in out}) != 1:
                    continue
                reach = 0
                for c in out:
                    reach |= balls[c]
                if reach == full:
                    v = n
                    n += 1
                    adj.append([])
                    deg.append(0)
                    color.append(1 if kind == 'P' else 0)
                    for c in out:
                        edges.append((c, v))
                        adj[c].append(v)
                        adj[v].append(c)
                        deg[c] += 1
                        deg[v] += 1
                    added = True
                    break
            if added:
                break
        if not added:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3 and d >= 3:
        qs = [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)]
        pg_cache = {}
        gf_cache = {}
        rounds = 0
        while time.monotonic() < deadline and qs and rounds < 300:
            for q in qs:
                if time.monotonic() >= deadline:
                    break
                s = d - q - 1
                if s < 0:
                    continue
                if q not in pg_cache:
                    pg_cache[q] = _pg_data(q)
                m, edges, pl, lp, index, _pts = pg_cache[q]

                cands = []
                if s == 0:
                    cands.append([])
                else:
                    cands.append(_greedy_arc(m, s, pl, lp, rng, 25, deadline))
                    if s >= 2:
                        if q not in gf_cache:
                            gf_cache[q] = lib.GF(q)
                        cs = _conic_set(q, index, gf_cache[q])
                        if _loads_ok(cs, s, m, pl, lp):
                            cands.append(cs)

                for S in cands:
                    if not _loads_ok(S, s, m, pl, lp):
                        continue
                    n_a, e_a = _arc_graph(m, edges, pl, lp, S)
                    consider(n_a, e_a)
                    n_g, e_g = _pencil_grow(n_a, e_a, m, S, pl, lp, d, D, deadline, rng)
                    consider(n_g, e_g)
            rounds += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
