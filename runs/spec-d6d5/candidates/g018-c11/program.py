import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured fallback families: projective plane, generalized quadrangle,
# arc extensions, and cover/saturation growth. These guarantee a valid answer.
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
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
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
# NEW CONSTRUCTION: exact-criterion bi-Cayley graphs over many small groups.
#
# Group G with connection set S (|S| = d, identity in S WLOG). Vertices A_g and
# B_h; A_g ~ B_{g s} for s in S. Left multiplication is an automorphism that is
# transitive on each side, so the diameter is <= D iff BOTH A_1 and B_1 reach all
# 2G vertices within distance D. Each evaluation is two BFS runs over G elements,
# which is far cheaper than the general lift checks used before.
#
# The previous search only sampled semidirect products with k2 <= 12, so it
# never tried metacyclic groups such as Z_19 x| Z_18 (order 342, record 684 = 2*342).
# Here every metacyclic group Z_m x| Z_k of a given order is enumerated, and S is
# annealed under a time-based temperature schedule.
# ----------------------------------------------------------------------------

def _enum_groups(G):
    """All (m, k, r) with m*k = G giving lib.semidirect_group(m, k, r)."""
    out = []
    for m in range(2, G + 1):
        if G % m:
            continue
        k = G // m
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


class _CayleyEval:
    """Multiplication table of a group plus the unreached-vertex cost of a connection set."""

    def __init__(self, G, mul, inv, d, D):
        self.G = G
        self.d = d
        self.D = D
        self.T = [[mul(g, s) for s in range(G)] for g in range(G)]
        self.inv = [inv(s) for s in range(G)]

    def _reach(self, S, Si, side):
        """Number of vertices within D of the base vertex (A_1 if side == 0, B_1 if side == 1)."""
        G, T = self.G, self.T
        seen = (bytearray(G), bytearray(G))
        seen[side][0] = 1
        frontier = [0]
        count = 1
        cur = side
        for _ in range(self.D):
            mark = seen[1 - cur]
            nxt = []
            if cur == 0:
                # A_g -> B_{g s}
                for g in frontier:
                    row = T[g]
                    for s in S:
                        h = row[s]
                        if not mark[h]:
                            mark[h] = 1
                            nxt.append(h)
            else:
                # B_h -> A_{h s^{-1}}
                for h in frontier:
                    row = T[h]
                    for t in Si:
                        g = row[t]
                        if not mark[g]:
                            mark[g] = 1
                            nxt.append(g)
            count += len(nxt)
            frontier = nxt
            cur = 1 - cur
            if not frontier:
                break
        return count

    def cost(self, S):
        """Number of vertices NOT within D of A_1 or of B_1. Zero means valid."""
        Si = [self.inv[s] for s in S]
        return (self.G - self._reach(S, Si, 0)) + (self.G - self._reach(S, Si, 1))


def _anneal_cayley(ev, rng, t_end):
    """Metropolis search over S = {0} + (d-1 distinct non-identity elements) until t_end.

    Returns a valid connection set or None. Temperature falls linearly with elapsed time.
    """
    G, d = ev.G, ev.d
    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    S = [0] + rng.sample(range(1, G), d - 1)
    cost = ev.cost(S)
    best_S, best_c = list(S), cost
    temp = 3.0
    it = 0
    while cost > 0:
        it += 1
        if it & 15 == 0:
            now = time.monotonic()
            if now >= t_end:
                break
            temp = 3.0 * max(0.0, 1.0 - (now - t0) / span) + 0.3
        i = rng.randrange(1, d)
        x = rng.randrange(1, G)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = ev.cost(S)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            if cost < best_c:
                best_c, best_S = cost, list(S)
        else:
            S[i] = old
    return best_S if best_c == 0 else None


def _cayley_graph(ev, S):
    """Edges of the bi-Cayley graph: A_g = g, B_h = G + h, A_g ~ B_{g s}."""
    G, T = ev.G, ev.T
    E = [(g, G + T[g][s]) for g in range(G) for s in S]
    return 2 * G, E


def _cayley_search(d, D, best_G, g_start, moore, deadline, rng, consider,
                   window=40, slice_len=3.0):
    """Search bi-Cayley graphs over metacyclic groups of order in a window above the best so far.

    Returns the largest group order that produced an accepted graph.
    """
    found = best_G
    while time.monotonic() < deadline - 0.2:
        lo = max(g_start, found + 1)
        if 2 * lo > moore:
            break
        G = lo + rng.randrange(window)
        if G <= d:
            continue
        cands = _enum_groups(G)
        if not cands:
            continue
        m, k, r = rng.choice(cands)
        order, mul, inv = lib.semidirect_group(m, k, r)
        ev = _CayleyEval(order, mul, inv, d, D)
        t_end = min(deadline, time.monotonic() + slice_len)
        S = _anneal_cayley(ev, rng, t_end)
        if S is not None:
            n, e = _cayley_graph(ev, S)
            if consider(n, e):
                found = max(found, order)
    return found


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.15 * time_limit, rng)
            consider(n2, e2)
        for n_c, e_c in _arc_extensions(d, start + 0.1 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.2 * time_limit, rng)
            consider(n2, e2)

    moore = lib._moore_bound(d, D)
    if best_n >= moore:
        return best

    # Main search: bi-Cayley graphs over metacyclic groups (new construction).
    if d >= 2 and D >= 2:
        g_start = max(best_n // 2, int(0.20 * moore))
        _cayley_search(d, D, best_n // 2, g_start, moore, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
