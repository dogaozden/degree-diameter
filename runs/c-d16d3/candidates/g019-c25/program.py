import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane based constructions (diameter 3) and generalized quadrangle
# (diameter 4), followed by a new randomized vertex-insertion search.
#
# The insertion search is a different construction from the parent's static
# A/B-side scheme. It starts from a valid graph and repeatedly adds one new
# vertex x on a chosen side. The new vertex is joined to a set N of opposite-side
# vertices that still have spare degree. N is chosen greedily to cover all
# same-side vertices at distance 2. Since adding a vertex and edges never
# lengthens any existing path, only distances from x need checking. The check is
# one BFS of depth D from x. Every accepted graph is therefore valid by
# construction, and lib.is_valid re-checks the final result.
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


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
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


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


def _pg_start(q):
    """Plain PG(2, q) incidence graph (degree q+1, diameter 3)."""
    m, edges, _, _, _, _ = _pg_data(q)
    return 2 * m, edges


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
# Randomized vertex insertion. Works on any bipartite graph with max degree d
# and diameter <= D. Every accepted state is valid.
# ----------------------------------------------------------------------------

class _Grower:
    def __init__(self, n, edges, d, D, rng):
        self.d = d
        self.D = D
        self.rng = rng
        self.adj = [[] for _ in range(n)]
        for u, v in edges:
            self.adj[u].append(v)
            self.adj[v].append(u)
        self.n = n
        col = [-1] * n
        for s in range(n):
            if col[s] != -1:
                continue
            col[s] = 0
            st = [s]
            while st:
                u = st.pop()
                for v in self.adj[u]:
                    if col[v] == -1:
                        col[v] = 1 - col[u]
                        st.append(v)
        self.col = col
        self.members = [[v for v in range(n) if col[v] == 0],
                        [v for v in range(n) if col[v] == 1]]

    def _reach_all(self, x):
        """True if BFS from x within D steps reaches every vertex."""
        seen = bytearray(self.n)
        seen[x] = 1
        frontier = [x]
        cnt = 1
        for _ in range(self.D):
            nxt = []
            for u in frontier:
                for v in self.adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        return cnt == self.n

    def _best_of(self, cands, cover, chosen_set):
        best = None
        bestv = 0
        for y in cands:
            if y in chosen_set:
                continue
            v = 0
            for w in self.adj[y]:
                if not cover[w]:
                    v += 1
            if v > bestv:
                bestv = v
                best = y
        return best, bestv

    def _pick(self, side, spare, sample):
        """Greedy choice of opposite-side neighbours covering all same-side vertices."""
        rng = self.rng
        need = len(self.members[side])
        cover = bytearray(self.n)
        covered = 0
        chosen = []
        chosen_set = set()
        while len(chosen) < self.d and covered < need:
            cands = rng.sample(spare, min(sample, len(spare)))
            best, bestv = self._best_of(cands, cover, chosen_set)
            if best is None and len(spare) > sample:
                best, bestv = self._best_of(spare, cover, chosen_set)
            if best is None:
                break
            chosen.append(best)
            chosen_set.add(best)
            for w in self.adj[best]:
                if not cover[w]:
                    cover[w] = 1
                    covered += 1
        if covered < need:
            return None
        return chosen

    def _add(self, side, N):
        """Add a new vertex on `side` joined to N, if the result keeps diameter <= D."""
        x = self.n
        self.adj.append(list(N))
        for y in N:
            self.adj[y].append(x)
        self.n += 1
        if not self._reach_all(x):
            for y in N:
                self.adj[y].pop()
            self.adj.pop()
            self.n -= 1
            return False
        self.col.append(side)
        self.members[side].append(x)
        return True

    def grow(self, deadline):
        while time.monotonic() < deadline:
            side = self.rng.randrange(2)
            spare = [y for y in self.members[1 - side] if len(self.adj[y]) < self.d]
            if not spare:
                side = 1 - side
                spare = [y for y in self.members[1 - side] if len(self.adj[y]) < self.d]
                if not spare:
                    break
            N = self._pick(side, spare, 40)
            if not N:
                continue
            self._add(side, N)
        edges = [(u, v) for u in range(self.n) for v in self.adj[u] if u < v]
        return self.n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.8 * time_limit
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

    if D == 2:
        return best

    starts = []
    if D >= 3:
        arc_deadline = start + 0.25 * time_limit
        for n_c, e_c in _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d)):
            consider(n_c, e_c)
            if lib.is_valid(n_c, e_c, d, D):
                starts.append((n_c, e_c))
        qs = [q for q in range(2, min(d - 2, 23) + 1) if lib.is_prime_power(q)]
        for q in sorted(qs, reverse=True)[:3]:
            n0, e0 = _pg_start(q)
            if lib.is_valid(n0, e0, d, D):
                starts.append((n0, e0))

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None and lib.is_valid(gq[0], gq[1], d, D):
            starts.append(gq)

    # Insertion search: each start gets an equal share of the remaining time.
    for i, (n0, e0) in enumerate(starts):
        now = time.monotonic()
        if now >= end:
            break
        share = (end - now) / (len(starts) - i)
        g = _Grower(n0, e0, d, D, random.Random(rng.randrange(1 << 30)))
        n_g, e_g = g.grow(now + share)
        consider(n_g, e_g)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
