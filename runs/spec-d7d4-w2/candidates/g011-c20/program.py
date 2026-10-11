import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: generalized quadrangles W(q) (D >= 4) and projective planes (D = 3).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Shared utilities.
# ----------------------------------------------------------------------------

def _adj_list(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _incidence(P, edges):
    """Point->line and line->point lists for a bipartite graph with points 0..P-1 and lines P..2P-1."""
    point_lines = [[] for _ in range(P)]
    line_points = [[] for _ in range(P)]
    for u, v in edges:
        point_lines[u].append(v - P)
        line_points[v - P].append(u)
    return point_lines, line_points


# ----------------------------------------------------------------------------
# NEW: layered twin packing driven by a max-independent-set search.
#
# A twin of a point x is a new point-side vertex with the same neighbourhood as x.
# Twins preserve the diameter (twin-to-anything distances equal the original's).
# With slack s per vertex, s "layers" of twins fit: in one layer, a set of points
# with no two collinear loads every line by at most 1. Likewise, a layer of lines
# with no two meeting loads every point by at most 1. Point-twins load lines and
# line-twins load points, so the two sides never interact.
# ----------------------------------------------------------------------------

def _conflicts(P, point_lines, line_points):
    """Collinearity graph on points and intersection graph on lines."""
    pc = [set() for _ in range(P)]
    for pts in line_points:
        for a in pts:
            for b in pts:
                if a != b:
                    pc[a].add(b)
    lc = [set() for _ in range(P)]
    for p in range(P):
        ls = point_lines[p]
        for a in ls:
            for b in ls:
                if a != b:
                    lc[a].add(b)
    return [sorted(s) for s in pc], [sorted(s) for s in lc]


def _mis(adj, rng, deadline, iters):
    """Randomized (1,2)-swap style local search for a large independent set. Returns best found."""
    N = len(adj)
    inS = [False] * N
    tight = [0] * N
    S = []

    def put(v):
        inS[v] = True
        S.append(v)
        for u in adj[v]:
            tight[u] += 1

    def out(v):
        inS[v] = False
        S.remove(v)
        for u in adj[v]:
            tight[u] -= 1

    order = list(range(N))
    rng.shuffle(order)
    for v in order:
        if not inS[v] and tight[v] == 0:
            put(v)
    best = list(S)
    for _ in range(iters):
        if time.monotonic() >= deadline:
            break
        pool = [v for v in range(N) if not inS[v] and tight[v] <= 2]
        if not pool:
            pool = [v for v in range(N) if not inS[v]]
            if not pool:
                break
        v = rng.choice(pool)
        for u in adj[v]:
            if inS[u]:
                out(u)
        put(v)
        free = [u for u in range(N) if not inS[u] and tight[u] == 0]
        rng.shuffle(free)
        for u in free:
            if not inS[u] and tight[u] == 0:
                put(u)
        if len(S) > len(best):
            best = list(S)
        elif len(S) < len(best) - 1:
            for u in list(S):
                out(u)
            for u in best:
                put(u)
    return best


def _layers(conf, s, rng, deadline):
    """Return s independent sets, each found by repeated MIS restarts within its time share."""
    out = []
    for j in range(s):
        now = time.monotonic()
        end = now + (deadline - now) / (s - j)
        best = []
        restarts = 0
        while time.monotonic() < end and restarts < 60:
            r = _mis(conf, rng, end, 1500)
            restarts += 1
            if len(r) > len(best):
                best = r
        out.append(best)
    return out


def _build_twins(P, edges, point_lines, line_points, s, rng, deadline):
    pc, lc = _conflicts(P, point_lines, line_points)
    now = time.monotonic()
    mid = now + (deadline - now) / 2
    pl = _layers(pc, s, rng, mid)
    ll = _layers(lc, s, rng, deadline)
    N = 2 * P
    E = list(edges)
    for I in pl:
        for x in I:
            v = N
            N += 1
            for l in point_lines[x]:
                E.append((v, P + l))
    for I in ll:
        for L in I:
            v = N
            N += 1
            for p in line_points[L]:
                E.append((p, v))
    return N, E


def _saturate_edges(n, edges, d, rng):
    """Join deficient opposite-side vertices with leftover spare degree (only shortens distances)."""
    edges = list(edges)
    adj = _adj_list(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    budget_end = start + 0.5 * time_limit
    try:
        if D == 3:
            qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:1]
        else:
            qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]

        for idx, q in enumerate(qs):
            if D == 3:
                n0, e0 = lib.projective_plane_incidence(q)
            else:
                n0, e0 = _gq_w(q)
            consider(n0, e0)

            s = d - q - 1
            if s <= 0:
                continue
            now = time.monotonic()
            share = max(0.0, budget_end - now) / (len(qs) - idx)
            P = n0 // 2
            point_lines, line_points = _incidence(P, e0)
            n2, e2 = _build_twins(P, e0, point_lines, line_points, s, rng, now + share)
            e2 = _saturate_edges(n2, e2, d, rng)
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
