import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. Choose a point set S such that every line contains at most s
# points of S and every point lies on at most s lines indexed by S. For each
# P in S add a new A-vertex joined to the q+1 lines through P; for each j in S
# add a new B-vertex joined to the q+1 points on line j. Order 2(q^2+q+1)+2|S|.
#
# For d=16, q=13 the arc S is a conic (14 points), giving 394.
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


def _arc_graph(m, edges, S, point_lines, line_points):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
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
    """Return candidates (n, edges, m, point_lines, line_points) for each prime power q with q + 1 <= d."""
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
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, S, point_lines, line_points)
        out.append((n_c, e_c, m, point_lines, line_points))
    return out


# ----------------------------------------------------------------------------
# Incremental bipartite graph state with undo, used by the D = 3 local search.
#
# Every vertex has a fixed side (0 or 1) and edges only join opposite sides,
# so the graph stays bipartite. Bitmasks ball2 give cheap distance checks:
#   * adding a vertex x adjacent to N keeps diameter <= 3 iff every alive vertex
#     lies within distance 2 of some u in N (old distances can only shrink);
#   * removing vertices can break distances, so exchange moves get a full check.
# ----------------------------------------------------------------------------

class _Graph:
    def __init__(self, cap, side):
        self.cap = cap
        self.adj = [set() for _ in range(cap)]
        self.am = [0] * cap
        self.side = list(side) + [0] * (cap - len(side))
        self.alive = 0
        self.nxt = 0
        self.free = []
        self.log = None
        self.saved = None

    def _raw_link(self, u, v):
        self.adj[u].add(v)
        self.adj[v].add(u)
        self.am[u] |= 1 << v
        self.am[v] |= 1 << u
        self.alive |= (1 << u) | (1 << v)

    def _raw_unlink(self, u, v):
        self.adj[u].discard(v)
        self.adj[v].discard(u)
        self.am[u] &= ~(1 << v)
        self.am[v] &= ~(1 << u)
        if not self.adj[u]:
            self.alive &= ~(1 << u)
        if not self.adj[v]:
            self.alive &= ~(1 << v)

    def link(self, u, v):
        self._raw_link(u, v)
        if self.log is not None:
            self.log.append((True, u, v))

    def unlink(self, u, v):
        self._raw_unlink(u, v)
        if self.log is not None:
            self.log.append((False, u, v))

    def load(self, edges, side):
        for v in range(self.cap):
            self.adj[v] = set()
            self.am[v] = 0
        self.side = list(side) + [0] * (self.cap - len(side))
        self.alive = 0
        self.log = None
        top = -1
        for u, v in edges:
            self._raw_link(u, v)
            top = max(top, u, v)
        self.nxt = top + 1
        self.free = [v for v in range(self.nxt) if not self.adj[v]]

    def count(self):
        return self.alive.bit_count()

    def edges(self):
        return [(u, v) for u in range(self.nxt) for v in self.adj[u] if u < v]

    def ball2(self, u):
        b = self.am[u] | (1 << u)
        am = self.am
        for w in self.adj[u]:
            b |= am[w]
        return b

    def new_vertex(self, s):
        if self.free:
            x = self.free.pop()
        elif self.nxt < self.cap:
            x = self.nxt
            self.nxt += 1
        else:
            return None
        self.side[x] = s
        return x

    def try_add(self, nb, s):
        """Add a vertex on side s joined to nb (all alive, on side 1-s) if diameter stays <= 3."""
        cov = 0
        for u in nb:
            cov |= self.ball2(u)
        if (cov & self.alive) != self.alive:
            return False
        x = self.new_vertex(s)
        if x is None:
            return False
        for u in nb:
            self.link(x, u)
        return True

    def remove_vertex(self, v):
        for u in list(self.adj[v]):
            self.unlink(v, u)
        self.free.append(v)

    def valid_full(self):
        verts = [v for v in range(self.nxt) if self.adj[v]]
        b2 = {}
        for v in verts:
            b2[v] = self.ball2(v)
        AM = self.alive
        for v in verts:
            b3 = 1 << v
            for u in self.adj[v]:
                b3 |= b2[u]
            if (b3 & AM) != AM:
                return False
        return True

    def begin(self):
        self.log = []
        self.saved = (self.nxt, list(self.free), list(self.side))

    def commit(self):
        self.log = None

    def rollback(self):
        for is_link, u, v in reversed(self.log):
            if is_link:
                self._raw_unlink(u, v)
            else:
                self._raw_link(u, v)
        self.nxt, self.free, self.side = self.saved[0], self.saved[1], self.saved[2]
        self.log = None


def _star(c, pl, lp, m, g, d):
    """Star at PG vertex c: returns (side, neighbours) with neighbours filtered for spare degree, or None."""
    if c < m:
        s = 0
        cand = [m + L for L in pl[c]]
    else:
        s = 1
        cand = list(lp[c - m])
    nb = [u for u in cand
          if g.adj[u] and len(g.adj[u]) < d and g.side[u] == 1 - s]
    return (s, nb) if len(nb) >= 2 else (s, None)


def _center_near(f, pl, lp, m, rng):
    """A random PG centre whose star contains vertex f (or a random centre if f is not a PG vertex)."""
    if f < m:
        return m + rng.choice(pl[f])
    if f < 2 * m:
        return rng.choice(lp[f - m])
    return rng.randrange(2 * m)


def _grow(g, pl, lp, m, d, rng, tries):
    """Try random stars until one can be added without breaking diameter 3."""
    for _ in range(tries):
        c = rng.randrange(2 * m)
        s, nb = _star(c, pl, lp, m, g, d)
        if nb is not None and g.try_add(nb, s):
            return True
    return False


# ----------------------------------------------------------------------------
# Local search on the arc graph (D = 3).
#
# Moves:
#   * grow: add a star vertex whose addition is certified by ball2 coverage;
#   * exchange: remove a random vertex, then try to re-add stars that use the
#     freed capacity of its former neighbours. Accepted with an annealing rule
#     on the vertex count, and only if the full diameter check passes.
# The best valid graph is returned, so every result is valid.
# ----------------------------------------------------------------------------

def _local_search(n0, E0, m, pl, lp, d, D, deadline, rng):
    k = (n0 - 2 * m) // 2
    side = [0] * n0
    for v in range(m, 2 * m):
        side[v] = 1
    for v in range(2 * m + k, n0):
        side[v] = 1

    g = _Graph(n0 + 128, side)
    g.load(E0, side)
    best_E = g.edges()
    best_side = list(g.side)
    best_cnt = g.count()
    cur = best_cnt
    stale = 0
    T = 0.5

    while time.monotonic() < deadline:
        stale += 1
        if stale > 3000:
            g.load(best_E, best_side)
            cur = best_cnt
            stale = 0
            continue

        if rng.random() < 0.4:
            if _grow(g, pl, lp, m, d, rng, 12):
                cur = g.count()
                if cur > best_cnt:
                    best_cnt = cur
                    best_E = g.edges()
                    best_side = list(g.side)
                    stale = 0
            continue

        g.begin()
        before = cur
        v = rng.randrange(g.nxt)
        while not g.adj[v]:
            v = rng.randrange(g.nxt)
        freed = list(g.adj[v])
        g.remove_vertex(v)
        for _ in range(10):
            f = rng.choice(freed)
            c = _center_near(f, pl, lp, m, rng)
            s, nb = _star(c, pl, lp, m, g, d)
            if nb is not None:
                g.try_add(nb, s)
        after = g.count()
        delta = after - before
        accept = delta >= 0 or rng.random() < math.exp(delta / T)
        if accept and g.valid_full():
            g.commit()
            cur = after
            if cur > best_cnt:
                best_cnt = cur
                best_E = g.edges()
                best_side = list(g.side)
                stale = 0
        else:
            g.rollback()

    n, E = lib.relabel(best_E)
    if lib.is_valid(n, E, d, D):
        return n, E
    return None


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (unchanged from parent).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Arc-extended projective plane graphs. Diameter 3, so valid for all D >= 3.
    if D >= 3:
        cands = _arc_extensions(d, start + 0.25 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for c in cands:
            consider(c[0], c[1])

        # Incremental, validity-tracked local search from the largest arc graph.
        if D == 3 and cands:
            n_c, e_c, m, pl, lp = cands[0]
            res = _local_search(n_c, e_c, m, pl, lp, d, D,
                                start + 0.85 * time_limit, random.Random(seed * 31 + 7))
            if res is not None:
                consider(res[0], res[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: annealed group voltage lifts. For D >= 5 use larger bases.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
