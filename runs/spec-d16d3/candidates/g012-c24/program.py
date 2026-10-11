import itertools
import math
import random
import time

import lib

# Bold variant: after the projective-plane arc extension (diameter 3), run simulated
# annealing over bipartite graphs. Moves add edges or move one endpoint of an edge
# (degree <= d and bipartiteness are kept as hard constraints). The cost is the number
# of vertex pairs at distance > D. When cost reaches 0 the graph is validated and two
# vertices (one per side) are added. Every returned graph passes lib.is_valid, and the
# fallback is K_{d,d} (or the best arc/GQ graph found), so each case returns a valid graph.
# Note: for d=16, q=13 a covering argument shows the arc-extension family is forced to
# pencils, so any gain must come from non-local structure. This search is not guaranteed
# to beat 394.


# ----------------------------------------------------------------------------
# Projective-plane arc extension (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s A-attachments and every point <= s B-attachments."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s."""
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
    """PG incidence plus a new A-vertex per S-point (joined to its lines) and a new B-vertex per S-line."""
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
    """Return a list of (n, edges) arc-extended graphs, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bipartite graphs (the bold new search).
# ----------------------------------------------------------------------------

def _two_colour(adj):
    """Return a 0/1 side label per vertex (bipartition from BFS)."""
    n = len(adj)
    side = [-1] * n
    for s in range(n):
        if side[s] != -1:
            continue
        side[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if side[v] == -1:
                    side[v] = 1 - side[u]
                    stack.append(v)
    return side


def _cost(adj, D):
    """Number of unordered vertex pairs at distance > D (zero means diameter <= D)."""
    n = len(adj)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _sa_extend(d, D, n0, edges0, deadline, rng):
    """Anneal from a valid graph: add a vertex pair, then repair until diameter <= D again."""
    adj = [set() for _ in range(n0)]
    for u, v in edges0:
        adj[u].add(v)
        adj[v].add(u)
    side = _two_colour(adj)
    sides = [[], []]
    for v in range(n0):
        sides[side[v]].append(v)
    moore = lib._moore_bound(d, D)
    if n0 + 2 > moore:
        return None

    def add_pair():
        for s in (0, 1):
            adj.append(set())
            side.append(s)
            sides[s].append(len(adj) - 1)

    add_pair()
    cur = _cost(adj, D)
    result = None
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)

    while time.monotonic() < deadline:
        if cur == 0:
            n = len(adj)
            E = [(u, v) for u in range(n) for v in adj[u] if u < v]
            if lib.is_valid(n, E, d, D):
                result = (n, E)
            if n + 2 > moore:
                break
            add_pair()
            cur = _cost(adj, D)
            continue

        frac = (time.monotonic() - t0) / span
        T = max(0.1, 2.0 * (1.0 - frac))

        if rng.random() < 0.3:
            # Add an edge between a free vertex on each side.
            a = rng.choice(sides[0])
            b = rng.choice(sides[1])
            if len(adj[a]) >= d or len(adj[b]) >= d or b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            new = _cost(adj, D)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
            else:
                adj[a].discard(b)
                adj[b].discard(a)
        else:
            # Move one endpoint of an edge (u,v) to another vertex w on v's side.
            u = rng.randrange(len(adj))
            if not adj[u]:
                continue
            v = rng.choice(list(adj[u]))
            w = rng.choice(sides[side[v]])
            if w == v or w in adj[u] or len(adj[w]) >= d:
                continue
            adj[u].discard(v)
            adj[v].discard(u)
            adj[u].add(w)
            adj[w].add(u)
            new = _cost(adj, D)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
            else:
                adj[u].discard(w)
                adj[w].discard(u)
                adj[u].add(v)
                adj[v].add(u)

    return result


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        n_c, e_c = cand
        if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)

    if D >= 3:
        for cand in _arc_candidates(d, start + 0.2 * time_limit, rng):
            consider(cand)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    if D >= 3 and time.monotonic() < deadline:
        res = _sa_extend(d, D, best[0], best[1], deadline, rng)
        if res is not None:
            consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
