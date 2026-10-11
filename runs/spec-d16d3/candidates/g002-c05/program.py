import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane bases.
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


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
# Adds an A-vertex per point of S and a B-vertex per line of S, where S has
# every line holding <= s points of S and every point on <= s lines of S.
# ----------------------------------------------------------------------------

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
# Cover-vertex insertion by simulated annealing (new routine).
#
# A new vertex v on side c with neighbours N (opposite side, deg < d) keeps the
# diameter <= D iff the radius-(D-1) balls of N cover every vertex of the graph:
# dist(v, x) <= D  <=>  some u in N has dist(u, x) <= D - 1.
# Adding a vertex never shortens distances between old vertices, so validity
# is preserved. We search for such a cover of size <= d with annealing on the
# number of uncovered vertices, which is more flexible than greedy set cover.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
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


def _bipartition(n, adj):
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


def _sa_cover(n, cb, d, rng, iters, deadline):
    """Find <= d candidates whose covered-index lists cover all n indices.

    cb[i] is the list of vertex indices covered by candidate i.
    Returns a list of candidate indices, or None.
    """
    m = len(cb)
    cap = min(d, m)
    if cap == 0:
        return None
    cnt = [0] * n
    st = [n]  # st[0] = number of uncovered vertices
    in_set = [False] * m
    chosen = []

    def apply(i, sgn):
        u = st[0]
        if sgn > 0:
            for x in cb[i]:
                if cnt[x] == 0:
                    u -= 1
                cnt[x] += 1
        else:
            for x in cb[i]:
                cnt[x] -= 1
                if cnt[x] == 0:
                    u += 1
        st[0] = u

    def pick_out():
        while True:
            j = rng.randrange(m)
            if not in_set[j]:
                return j

    for i in rng.sample(range(m), cap):
        apply(i, 1)
        in_set[i] = True
        chosen.append(i)

    T0, T1 = 1.0, 0.05
    for it in range(iters):
        if st[0] == 0:
            break
        if it & 63 == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        old = st[0]
        if len(chosen) < cap and (not chosen or rng.random() < 0.5):
            j = pick_out()
            apply(j, 1)
            in_set[j] = True
            chosen.append(j)
            continue
        if len(chosen) >= m:
            break
        pos = rng.randrange(len(chosen))
        i = chosen[pos]
        j = pick_out()
        apply(i, -1)
        apply(j, 1)
        delta = st[0] - old
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            chosen[pos] = j
            in_set[i] = False
            in_set[j] = True
        else:
            apply(j, -1)
            apply(i, 1)

    if st[0] == 0:
        return chosen
    return None


def _sa_grow(n, edges, d, D, deadline, rng, iters):
    """Repeatedly add a vertex with an annealed cover until no side succeeds."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        sides = [0, 1]
        rng.shuffle(sides)
        added = False
        for c in sides:
            if time.monotonic() >= deadline:
                break
            cands = [s for s in range(n) if color[s] == 1 - c and deg[s] < d]
            if not cands:
                continue
            cb = [[x for x in range(n) if (ball[s] >> x) & 1] for s in cands]
            chosen = _sa_cover(n, cb, d, rng, iters, deadline)
            if chosen is None:
                continue
            v = n
            n += 1
            adj.append([])
            deg.append(0)
            color.append(c)
            for i in chosen:
                s = cands[i]
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

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        starts = []
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            starts.append(pg)
        arcs = _arc_extensions(d, start + 0.2 * time_limit,
                               random.Random(seed * 7919 + d))
        arcs.sort(key=lambda g: -g[0])
        for g in arcs[:3]:
            consider(g[0], g[1])
            starts.append(g)

        # Spend the search budget on cover insertion from each start.
        for idx, g in enumerate(starts):
            now = time.monotonic()
            if now >= deadline:
                break
            share = (deadline - now) / (len(starts) - idx)
            n2, e2 = _sa_grow(g[0], g[1], d, D, now + share, rng, 4000)
            consider(n2, e2)

        # Leftover time: retry growth from the current best graph.
        if time.monotonic() < deadline:
            n2, e2 = _sa_grow(best_n, best[1], d, D, deadline, rng, 4000)
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
