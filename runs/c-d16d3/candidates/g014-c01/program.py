import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base construction: arc-extended projective plane incidence graphs (D = 3).
# Old vertices have spare degree s = d - q - 1; a point set S with every line
# holding <= s points of S and every point on <= s lines of S gives new
# A-vertices (on pencils of S-points) and B-vertices (on lines of S).
# ----------------------------------------------------------------------------

def _pg_data(q):
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


def _arc_base(d, deadline, rng):
    """Largest valid arc-extended PG(2,q) graph over prime powers q with q + 1 <= d."""
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, pl, lp):
            continue
        n, E = _arc_graph(m, edges, pl, lp, S)
        if best is None or n > best[0]:
            best = (n, E)
    return best


# ----------------------------------------------------------------------------
# Repair search: grow the graph by inserting vertices with spare-capacity
# neighbours, then rewire edges by annealing on the number of vertex pairs
# farther apart than D. Bipartiteness is kept by only joining opposite colours.
# ----------------------------------------------------------------------------

def _bfs_colors(n, adj):
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


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance more than D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _edges_of(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _search(n0, E0, d, D, rng, deadline):
    """Return the largest validated graph found, starting from (n0, E0) which must be valid."""
    n = n0
    adj = [set() for _ in range(n)]
    for u, v in E0:
        adj[u].add(v)
        adj[v].add(u)
    color = _bfs_colors(n, adj)
    cur = _bad(n, adj, D)
    best_n, best = n0, (n0, list(E0))
    snap = (n, [set(s) for s in adj], list(color))
    since = 0
    idle = 0
    T = 0.3

    while time.monotonic() < deadline and idle < 3000:
        if cur == 0:
            snap = (n, [set(s) for s in adj], list(color))
            since = 0
            if n > best_n:
                E = _edges_of(n, adj)
                if lib.is_valid(n, E, d, D):
                    best_n, best = n, (n, E)
            # Try to grow: new vertex joined to spare vertices of the opposite side.
            if rng.random() < 0.5:
                side = rng.randrange(2)
                cand = []
                for sd in (side, 1 - side):
                    cand = [u for u in range(n) if color[u] == 1 - sd and len(adj[u]) < d]
                    if cand:
                        side = sd
                        break
                if cand:
                    k = min(d, len(cand))
                    chosen = rng.sample(cand, k)
                    w = n
                    n += 1
                    adj.append(set())
                    color.append(side)
                    for u in chosen:
                        adj[u].add(w)
                        adj[w].add(u)
                    cur = _bad(n, adj, D)
                    idle = 0
                    continue

        if cur > 0:
            since += 1
            if since > 600:
                n, adj, color = snap[0], [set(s) for s in snap[1]], list(snap[2])
                cur = 0
                since = 0
                continue

        # Rewire: remove a random edge, add a random spare cross edge.
        u = rng.randrange(n)
        if not adj[u]:
            idle += 1
            continue
        v = rng.choice(tuple(adj[u]))
        adj[u].discard(v)
        adj[v].discard(u)
        s0 = [x for x in range(n) if color[x] == 0 and len(adj[x]) < d]
        s1 = [x for x in range(n) if color[x] == 1 and len(adj[x]) < d]
        placed = None
        if s0 and s1:
            for _ in range(30):
                a = rng.choice(s0)
                b = rng.choice(s1)
                if b not in adj[a]:
                    placed = (a, b)
                    break
        if placed is None:
            adj[u].add(v)
            adj[v].add(u)
            idle += 1
            continue
        a, b = placed
        adj[a].add(b)
        adj[b].add(a)
        new = _bad(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            idle = 0
        else:
            adj[a].discard(b)
            adj[b].discard(a)
            adj[u].add(v)
            adj[v].add(u)
            idle += 1

    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        base = _arc_base(d, start + 0.15 * time_limit, rng)
        if base is not None and base[0] > best[0] and lib.is_valid(base[0], base[1], d, D):
            best = base

    n_s, E_s = _search(best[0], best[1], d, D, rng, start + 0.85 * time_limit)
    if n_s > best[0] and lib.is_valid(n_s, E_s, d, D):
        best = (n_s, E_s)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
