import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with degree cap d it has spare capacity s = d-q-1. Pick a point set S
# (an arc: every line holds <= s points of S). Add a new A-vertex per point of
# S (joined to the q+1 lines through it) and a new B-vertex per line of S
# (joined to the q+1 points on it). The diameter stays 3.
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
    """Randomized greedy arc with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG incidence plus a new A-vertex per point of S and a new B-vertex per line of S."""
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


def _arc_candidates(d, deadline, rng):
    """One (n, edges) candidate per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, _pts = _pg_data(q)
        S = []
        if s >= 1:
            S = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points) and len(cs) > len(S):
                S = cs
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# NEW HELPERS: twin augmentation with a 2-ball cover certificate, and a
# random spare-edge fill used for a plateau walk.
#
# Twin augmentation (D = 3 only): a new vertex w of colour(c) is joined to all
# neighbours N of some vertex c. The result has diameter <= 3 iff every vertex
# is within distance 2 of N, i.e. the union of the radius-2 balls of N is the
# whole vertex set. All vertices of N must have spare capacity below d.
# Adding edges never increases any distance, so a valid state stays valid.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _colors(n, adj):
    """Two-colouring by BFS (valid for bipartite graphs)."""
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


def _two_balls(n, adj):
    """Bitmask of all vertices at distance <= 2 from each vertex."""
    r1 = [0] * n
    for v in range(n):
        b = 1 << v
        for u in adj[v]:
            b |= 1 << u
        r1[v] = b
    B2 = [0] * n
    for v in range(n):
        b = r1[v]
        for u in adj[v]:
            b |= r1[u]
        B2[v] = b
    return B2


def _twin_augment(n, adj, color, d, deadline, rng):
    """Repeatedly add twins whose neighbourhood 2-covers everything. Returns the new n."""
    while time.monotonic() < deadline:
        B2 = _two_balls(n, adj)
        full = (1 << n) - 1
        order = list(range(n))
        rng.shuffle(order)
        added = False
        for c in order:
            N = adj[c]
            if not N or len(N) > d or any(len(adj[u]) >= d for u in N):
                continue
            cov = 0
            for u in N:
                cov |= B2[u]
            if cov != full:
                continue
            w = n
            n += 1
            adj.append(set(N))
            color.append(color[c])
            for u in N:
                adj[u].add(w)
            added = True
            break
        if not added:
            break
    return n


def _random_fill(n, adj, color, d, rng, tries):
    """Add random edges between spare vertices of opposite colours (never breaks validity)."""
    for _ in range(tries):
        L0 = [u for u in range(n) if color[u] == 0 and len(adj[u]) < d]
        L1 = [u for u in range(n) if color[u] == 1 and len(adj[u]) < d]
        if not L0 or not L1:
            return
        u = rng.choice(L0)
        v = rng.choice(L1)
        if v not in adj[u]:
            adj[u].add(v)
            adj[v].add(u)


def _to_edges(adj):
    return [(u, v) for u, nb in enumerate(adj) for v in sorted(nb) if u < v]


def _search_d3(d, deadline, rng):
    """Arc base, then twin augmentation with a random fill plateau walk. Returns (n, edges) or None."""
    cands = _arc_candidates(d, deadline, rng)
    if not cands:
        return None
    n0, E0 = max(cands, key=lambda t: t[0])
    adj = _adjacency(n0, E0)
    color = _colors(n0, adj)
    n_cur = _twin_augment(n0, adj, color, d, deadline, rng)
    best_n = n_cur
    best = (n_cur, _to_edges(adj))
    while time.monotonic() < deadline:
        a2 = [set(s) for s in adj]
        c2 = list(color)
        n2 = n_cur
        _random_fill(n2, a2, c2, d, rng, rng.randint(1, 6))
        n2 = _twin_augment(n2, a2, c2, d, deadline, rng)
        if n2 >= n_cur:
            adj, color, n_cur = a2, c2, n2
        if n2 > best_n:
            best_n = n2
            best = (n2, _to_edges(a2))
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) for D = 4 (kept from the parent).
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2: safe fallback for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    if D == 3:
        res = _search_d3(d, deadline, rng)
        if res is not None and res[0] > fallback[0] and lib.is_valid(res[0], res[1], d, D):
            return res
        return fallback

    # D >= 4: generalized quadrangle baseline when it fits.
    best = fallback
    gq = _best_gq(d)
    if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
        best = gq
    return best
