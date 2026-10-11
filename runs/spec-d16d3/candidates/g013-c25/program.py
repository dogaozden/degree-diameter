import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: projective planes, arc-extended planes, quadrangles.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _pp_list(d):
    """Prime powers q with 2 <= q <= min(d - 1, 23), largest first."""
    return [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)]


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


def _arc_info(q, cache):
    key = ("pg", q)
    if key not in cache:
        cache[key] = _pg_data(q)
    return cache[key]


def _gf(q, cache):
    key = ("gf", q)
    if key not in cache:
        cache[key] = lib.GF(q)
    return cache[key]


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


def _random_arc_base(d, rng, cache, deadline):
    """A fresh randomized arc-extended graph for a random top prime power, or None."""
    pps = _pp_list(d)[:3]
    if not pps:
        return None
    q = rng.choice(pps)
    s = d - q - 1
    if s < 1:
        return None
    m, edges, pl, lp, index, _pts = _arc_info(q, cache)
    if s >= 2 and rng.random() < 0.25:
        S = _conic_set(q, index, _gf(q, cache))
    else:
        S = _greedy_arc(m, s, pl, lp, rng, 1, deadline)
    if not S or not _loads_ok(S, s, m, pl, lp):
        return None
    return _arc_graph(m, edges, pl, lp, S)


# ----------------------------------------------------------------------------
# Neighbourhood-cover growth with spare-degree tabu search (D >= 3).
#
# A new vertex v of colour cv with neighbour set N keeps diameter <= D exactly
# when the radius-(D-1) balls of the vertices of N cover the whole old graph.
# Growth picks N among vertices with spare degree using tabu search on the
# number of uncovered vertices, instead of a single greedy pass.
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
        if new == ball:
            break
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


def _nth_bit(mask, k):
    """Index of the k-th (0-based) set bit of mask."""
    while k:
        mask &= mask - 1
        k -= 1
    return (mask & -mask).bit_length() - 1


def _tabu_cover(B, cands, F, d, rng, iters, deadline):
    """Choose at most d candidates whose ball masks cover F; tabu search on uncovered count."""
    chosen = []
    cov = 0
    while len(chosen) < d:
        unc = F & ~cov
        if not unc:
            return chosen
        bx, bg = None, 0
        for x in cands:
            if x in chosen:
                continue
            g = (B[x] & unc).bit_count()
            if g > bg or (g and g == bg and rng.random() < 0.5):
                bx, bg = x, g
        if bx is None:
            break
        chosen.append(bx)
        cov |= B[bx]

    tabu = {}
    for it in range(iters):
        unc = F & ~cov
        if not unc:
            return chosen
        if time.monotonic() > deadline:
            break
        u = _nth_bit(unc, rng.randrange(unc.bit_count()))
        opts = [x for x in cands
                if (B[x] >> u) & 1 and x not in chosen and tabu.get(x, -1) < it]
        if not opts:
            continue
        if len(chosen) < d:
            x = max(opts, key=lambda z: (B[z] & unc).bit_count())
            chosen.append(x)
            cov |= B[x]
            continue
        best = None
        for yi in range(len(chosen)):
            cov_wo = 0
            for j, z in enumerate(chosen):
                if j != yi:
                    cov_wo |= B[z]
            for x in opts:
                key = ((F & ~(cov_wo | B[x])).bit_count(), rng.random())
                if best is None or key < best[0]:
                    best = (key, yi, x)
        _, yi, x = best
        y = chosen[yi]
        chosen[yi] = x
        tabu[y] = it + 3 + rng.randrange(5)
        cov = 0
        for z in chosen:
            cov |= B[z]
    return chosen if not (F & ~cov) else None


def _grow_spare(n, edges, d, D, rng, deadline, max_misses):
    """Repeatedly add vertices whose neighbourhoods cover the graph within radius D-1."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    misses = 0
    while misses < max_misses and time.monotonic() < deadline:
        B = _balls_radius(n, adj, D - 1)
        F = (1 << n) - 1
        sides = [0, 1]
        rng.shuffle(sides)
        added = False
        for cv in sides:
            cands = [x for x in range(n) if color[x] != cv and deg[x] < d]
            if not cands:
                continue
            N = _tabu_cover(B, cands, F, d, rng, 150, deadline)
            if N is None:
                continue
            v = n
            n += 1
            adj.append([])
            deg.append(0)
            color.append(cv)
            for x in N:
                edges.append((x, v))
                adj[x].append(v)
                adj[v].append(x)
                deg[x] += 1
                deg[v] += 1
            added = True
            break
        misses = 0 if added else misses + 1
    return n, edges


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    cache = {}
    bases = []
    pg = _best_pg(d)
    if pg is not None:
        bases.append(pg)
    for q in _pp_list(d)[:3]:
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp, index, _pts = _arc_info(q, cache)
        S = _greedy_arc(m, s, pl, lp, rng, 40, deadline)
        if S and _loads_ok(S, s, m, pl, lp):
            bases.append(_arc_graph(m, edges, pl, lp, S))
        if s >= 2:
            cs = _conic_set(q, index, _gf(q, cache))
            if _loads_ok(cs, s, m, pl, lp):
                bases.append(_arc_graph(m, edges, pl, lp, cs))
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            bases.append(gq)

    valid_bases = []
    for n0, e0 in bases:
        if lib.is_valid(n0, e0, d, D):
            valid_bases.append((n0, e0))
            consider(n0, e0)
    if not valid_bases:
        return best

    top = max(valid_bases, key=lambda t: t[0])
    stale = 0
    rounds = 0
    while time.monotonic() < deadline and stale < 300:
        rounds += 1
        if rounds % 2 == 1:
            base = top
        else:
            base = _random_arc_base(d, rng, cache, deadline)
            if base is None or not lib.is_valid(base[0], base[1], d, D):
                base = top
        n2, e2 = _grow_spare(base[0], base[1], d, D, rng, deadline, 3)
        before = best[0]
        consider(n2, e2)
        if best[0] > before:
            stale = 0
        else:
            stale += 1
        if best[0] > top[0]:
            top = best

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
