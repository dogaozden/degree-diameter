import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane and generalized quadrangle bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
#
# From PG(2, q) incidence, spare capacity s = d - q - 1 per vertex. Pick a point
# set S with every line holding <= s points of S. Add an A-vertex per point of S
# (adjacent to the q+1 lines through it) and a B-vertex per line of S (adjacent to
# the q+1 points on it). Diameter stays 3 for any such S.
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
# Cover-based vertex extension and saturation.
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
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
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


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (only adds edges)."""
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
    """Repeatedly add a cover vertex (checked for validity), then saturate with spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        E = set((min(u, v), max(u, v)) for u, v in cur_e)
        adj = [[] for _ in range(cur_n)]
        for u, v in E:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        color = _bipartition(cur_n, adj)
        grown = False
        for c in (0, 1):
            cands = [s for s in range(cur_n) if color[s] == 1 - c and deg[s] < d]
            if not cands:
                continue
            ball = _balls_radius(cur_n, adj, D - 1)
            for attempt in range(60):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, (1 << cur_n) - 1, d, rng, attempt > 0)
                if chosen:
                    v = cur_n
                    E2 = E | {(min(s, v), max(s, v)) for s in chosen}
                    if lib.is_valid(cur_n + 1, list(E2), d, D):
                        E, cur_n, grown = E2, cur_n + 1, True
                    break
            if grown:
                break
        cur_e = _saturate_edges(cur_n, list(E), d, rng)
        if not grown:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW: cover-and-evict walk.
#
# Starting from a valid graph, repeatedly try to attach one new vertex whose
# neighbourhood covers everything within distance D-1 (a cover of all vertices
# by radius D-1 balls around the chosen neighbours). If no cover exists, make a
# perturbation: delete a random edge at a saturated vertex and re-add a random
# deficient opposite-side pair. A perturbation is kept only if the graph stays
# valid, so the walk never leaves the set of valid graphs. Growth happens only
# with a fully validated graph.
# ----------------------------------------------------------------------------

def _walk_extend(n, edges, d, D, deadline, rng):
    """Random walk over valid graphs that grows the vertex count when possible."""
    E = set((min(u, v), max(u, v)) for u, v in edges)
    cur_n = n
    best = (cur_n, list(E))
    while time.monotonic() < deadline:
        adj = [[] for _ in range(cur_n)]
        for u, v in E:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        color = _bipartition(cur_n, adj)
        c = rng.randrange(2)
        cands = [s for s in range(cur_n) if color[s] == 1 - c and deg[s] < d]
        grew = False
        if cands:
            ball = _balls_radius(cur_n, adj, D - 1)
            chosen = _greedy_cover(cands, ball, (1 << cur_n) - 1, d, rng, True)
            if chosen:
                v = cur_n
                E2 = E | {(min(s, v), max(s, v)) for s in chosen}
                if lib.is_valid(cur_n + 1, list(E2), d, D):
                    E, cur_n, grown = E2, cur_n + 1, True
                    grew = True
                    best = (cur_n, list(E))
        if grew:
            continue
        # Perturbation: drop one edge at a saturated vertex, add one deficient pair.
        sat = [s for s in range(cur_n) if deg[s] >= d]
        if not sat:
            break
        s = rng.choice(sat)
        t = rng.choice(adj[s])
        E2 = set(E)
        E2.discard((min(s, t), max(s, t)))
        deg2 = deg[:]
        deg2[s] -= 1
        deg2[t] -= 1
        L0 = [x for x in range(cur_n) if color[x] == 0 and deg2[x] < d]
        L1 = [x for x in range(cur_n) if color[x] == 1 and deg2[x] < d]
        if L0 and L1:
            for _ in range(20):
                a = rng.choice(L0)
                b = rng.choice(L1)
                key = (min(a, b), max(a, b))
                if key not in E2 and key != (min(s, t), max(s, t)):
                    E2.add(key)
                    break
        if lib.is_valid(cur_n, list(E2), d, D):
            E = E2
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.20 * time_limit, rng)
            consider(n2, e2)
        for n_c, e_c in _arc_extensions(d, start + 0.30 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.4 * time_limit, rng)
            consider(n2, e2)

    # New: cover-and-evict walk from the current best valid graph.
    if D >= 3 and d >= 5 and best_n > 2:
        n3, e3 = _walk_extend(best_n, best[1], d, D, deadline, rng)
        consider(n3, e3)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
