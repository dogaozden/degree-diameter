import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _ara(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
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


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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
# Shared bitmask / cover helpers.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
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
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails.

    `ball` maps each candidate to its bitmask.
    """
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the graph."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball_list = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            ball = {s: ball_list[s] for s in cands}
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
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


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
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


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices first, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW: ruin-and-recreate large-neighbourhood search on valid diameter-D graphs.
#
# A move removes k vertices close together (within distance 2 of a random
# vertex). The removal frees degree slots on their neighbours. Then k or k+1
# new vertices are inserted on the sides of the removed vertices. Each new
# vertex w picks neighbours on the opposite side by a greedy cover of all
# existing vertices by radius-(D-1) balls, so w reaches every old vertex
# within D. The move is kept only if the whole graph still has diameter <= D.
# Plateau moves (k removed, k added) let the structure drift. Growth moves
# (k removed, k+1 added) increase the order. Afterwards spare degree is
# filled by edge saturation, which never breaks the diameter.
# ----------------------------------------------------------------------------

def _masks(order, A, r):
    """Index map, radius-r ball bitmasks (by index) and the full mask for the vertices in `order`."""
    idx = {v: i for i, v in enumerate(order)}
    N = len(order)
    nb = [[idx[u] for u in A[v]] for v in order]
    ball = [1 << i for i in range(N)]
    for _ in range(r):
        new = []
        for i in range(N):
            x = ball[i]
            for j in nb[i]:
                x |= ball[j]
            new.append(x)
        ball = new
    return idx, ball, (1 << N) - 1


def _saturate_dict(A, C, d, rng):
    """Add random edges between deficient opposite-side vertices (keeps diameter, adds degree)."""
    left = [v for v in A if C[v] == 0 and len(A[v]) < d]
    right = [v for v in A if C[v] == 1 and len(A[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in A[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(A[a]) < d and len(A[b]) < d and b not in A[a]:
            A[a].add(b)
            A[b].add(a)


def _ruin_recreate(n, edges, d, D, deadline, rng):
    """Large-neighbourhood search: returns (n, edges) of a valid graph, at least as large as the input."""
    A = {v: set() for v in range(n)}
    for u, v in edges:
        A[u].add(v)
        A[v].add(u)
    cl = _bipartition(n, [sorted(A[v]) for v in range(n)])
    C = {v: cl[v] for v in range(n)}
    nxt = n

    while time.monotonic() < deadline:
        ids = list(A.keys())
        k = rng.choice((1, 2, 2, 3))
        u = rng.choice(ids)

        # Cluster: vertices within distance 2 of u.
        near = {u}
        frontier = {u}
        for _ in range(2):
            frontier = {w for x in frontier for w in A[x]} - near
            near |= frontier
        pool = list(near)
        if len(pool) < k:
            continue
        R = rng.sample(pool, k)

        grow = rng.random() < 0.5
        m = k + 1 if grow else k

        NA = {v: set(s) for v, s in A.items()}
        NC = dict(C)
        for r in R:
            for x in NA[r]:
                NA[x].discard(r)
        for r in R:
            del NA[r]
            del NC[r]

        newcols = [C[R[i % k]] for i in range(m)]
        ok = True
        nid = nxt
        for c in newcols:
            w = nid
            nid += 1
            NA[w] = set()
            NC[w] = c
            order = list(NA.keys())
            idx, ball, full = _masks(order, NA, D - 1)
            cands = [v for v in order if NC[v] == 1 - c and len(NA[v]) < d]
            ballv = {v: ball[idx[v]] for v in cands}
            target = full & ~(1 << idx[w])
            chosen = _greedy_cover(cands, ballv, target, d, rng, True)
            if not chosen:
                ok = False
                break
            for s in chosen:
                NA[s].add(w)
                NA[w].add(s)
        if not ok:
            continue

        order = list(NA.keys())
        _, ball, full = _masks(order, NA, D)
        if any(b != full for b in ball):
            continue

        nxt = nid
        A, C = NA, NC
        _saturate_dict(A, C, d, rng)

    order = list(A.keys())
    idx = {v: i for i, v in enumerate(order)}
    E = sorted({(min(idx[u], idx[v]), max(idx[u], idx[v]))
                for u in A for v in A[u]})
    return len(order), [(a, b) for a, b in E]


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
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
        # 1. Record-level construction when d - 2 is a prime power.
        ara = _ara(d)
        if ara is not None:
            consider(ara[0], ara[1])

        # 2. Plain projective plane incidence.
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # 3. Arc-extended projective plane graphs.
        for n_c, e_c in _arc_extensions(d, start + 0.12 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

        # 4. Cover extension and saturation of the best candidate.
        n2, e2 = _grow(best_n, best[1], d, D, start + 0.2 * time_limit, rng)
        consider(n2, e2)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.25 * time_limit, rng)
            consider(n2, e2)

    # 5. Ruin-and-recreate search from the best valid graph found so far.
    if D >= 3 and best_n >= 3:
        n3, e3 = _ruin_recreate(best_n, best[1], d, D,
                                start + 0.8 * time_limit,
                                random.Random(seed * 31 + 17))
        consider(n3, e3)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
