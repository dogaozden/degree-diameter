import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Diameter-3 bipartite graphs and common-neighbour covering.
#
# In a bipartite graph, two vertices on the same side are at even distance, so
# "distance <= 3" for same-side pairs means "distance 2", i.e. a common
# neighbour. If every same-side pair has a common neighbour and every vertex has
# a neighbour, then any X-vertex x and Y-vertex y not adjacent are joined by
# x - M - x' - y, where x' is any neighbour of y. So the diameter is <= 3 exactly
# when all same-side pairs are covered.
#
# Bold change: instead of adding gadgets to PG(2,q), keep a bipartite graph with
# fixed side sizes and minimise U = number of same-side pairs with no common
# neighbour. Moves are edge additions, edge relocations and degree-preserving
# double-edge swaps, all respecting the degree cap d. The search starts from the
# arc-extended PG(2,q) graph (order 394 for d = 16), adds one isolated vertex per
# side, and anneals. Each time U reaches 0 the graph is valid: it is recorded
# (after lib.is_valid), one more vertex per side is added, and the search
# continues. The best verified graph is always returned. Whether this beats the
# record is not guaranteed.
#
# For D >= 4 the same search runs (diameter 3 is valid for any D >= 3), so those
# cases may fall below what a D >= 4 specialist would achieve.
# ----------------------------------------------------------------------------


def _moore3(d):
    """Moore bound for bipartite graphs of diameter 3 and max degree d."""
    return 2 * (1 + (d - 1) + (d - 1) ** 2)


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


def _arc_base(d, q, rng, deadline):
    """Arc-extended PG(2,q) graph as (nX, nY, pairs).

    X = points (0..m-1) plus A-vertices (m..m+k-1); Y = lines (0..m-1) plus
    B-vertices (m..m+k-1). For each P in S, A_P joins all lines through P; for
    each j in S, B_j joins all points on line j. Degrees stay <= d.
    """
    s = d - q - 1
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    S = []
    if s >= 1:
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)]
        if s >= 2:
            F = lib.GF(q)
            index = {p: i for i, p in enumerate(lib.projective_points(q))}
            cs = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
            if q % 2 == 0:
                cs.append(index[(0, 1, 0)])
            cands.append(cs)
        cands = [c for c in cands if _loads_ok(c, s, m, point_lines, line_points)]
        S = max(cands, key=len, default=[])
    pairs = [(u, v - m) for u, v in edges]
    for t, P in enumerate(S):
        for L in point_lines[P]:
            pairs.append((m + t, L))
    for t, j in enumerate(S):
        for Q in line_points[j]:
            pairs.append((Q, m + t))
    k = m + len(S)
    return k, k, pairs


class _CoverSearch:
    """Bipartite graph with sides X (nX) and Y (nY), degree cap d.

    U = number of same-side pairs with no common neighbour. cX[x][x2] and
    cY[y][y2] count common neighbours of the pair, so U is maintained exactly
    under every edge change.
    """

    def __init__(self, d, rng, t_start):
        self.d = d
        self.rng = rng
        self.t_start = t_start
        self.nX = 0
        self.nY = 0
        self.adjX = []
        self.adjY = []
        self.cX = []
        self.cY = []
        self.U = 0

    def init(self, nX, nY, pairs):
        self.nX, self.nY = nX, nY
        self.adjX = [set() for _ in range(nX)]
        self.adjY = [set() for _ in range(nY)]
        self.cX = [[0] * nX for _ in range(nX)]
        self.cY = [[0] * nY for _ in range(nY)]
        self.U = nX * (nX - 1) // 2 + nY * (nY - 1) // 2
        for x, y in pairs:
            self._add(x, y)

    def grow(self):
        """Add one isolated vertex to each side."""
        a, b = self.nX, self.nY
        for row in self.cX:
            row.append(0)
        self.cX.append([0] * (a + 1))
        self.adjX.append(set())
        for row in self.cY:
            row.append(0)
        self.cY.append([0] * (b + 1))
        self.adjY.append(set())
        self.U += a + b
        self.nX, self.nY = a + 1, b + 1

    def _add(self, x, y):
        cX, cY, adjX, adjY = self.cX, self.cY, self.adjX, self.adjY
        U = self.U
        cx = cX[x]
        for x2 in adjY[y]:
            c = cx[x2]
            if c == 0:
                U -= 1
            cx[x2] = c + 1
            cX[x2][x] = c + 1
        cy = cY[y]
        for y2 in adjX[x]:
            c = cy[y2]
            if c == 0:
                U -= 1
            cy[y2] = c + 1
            cY[y2][y] = c + 1
        adjX[x].add(y)
        adjY[y].add(x)
        self.U = U

    def _remove(self, x, y):
        cX, cY, adjX, adjY = self.cX, self.cY, self.adjX, self.adjY
        adjX[x].discard(y)
        adjY[y].discard(x)
        U = self.U
        cx = cX[x]
        for x2 in adjY[y]:
            c = cx[x2] - 1
            if c == 0:
                U += 1
            cx[x2] = c
            cX[x2][x] = c
        cy = cY[y]
        for y2 in adjX[x]:
            c = cy[y2] - 1
            if c == 0:
                U += 1
            cy[y2] = c
            cY[y2][y] = c
        self.U = U

    def anneal(self, deadline, t0, t1, cycles):
        """Simulated annealing on U with cyclic geometric temperature; stops at U == 0 or deadline."""
        rng = self.rng
        d = self.d
        span = max(1e-3, deadline - self.t_start)
        T = t0
        it = 0
        while self.U > 0:
            it += 1
            if (it & 255) == 0:
                now = time.monotonic()
                if now >= deadline:
                    return
                f = ((now - self.t_start) / span * cycles) % 1.0
                T = t0 * (t1 / t0) ** f
            nX, nY = self.nX, self.nY
            adjX, adjY = self.adjX, self.adjY
            before = self.U
            r = rng.random()

            if r < 0.3:
                # Add an edge if both endpoints have spare degree. Never increases U.
                x = rng.randrange(nX)
                y = rng.randrange(nY)
                if y not in adjX[x] and len(adjX[x]) < d and len(adjY[y]) < d:
                    self._add(x, y)
                continue

            if r < 0.55:
                # Move the Y-end of an edge at x to a Y-vertex with spare degree.
                x = rng.randrange(nX)
                if not adjX[x]:
                    continue
                y = rng.choice(list(adjX[x]))
                y2 = rng.randrange(nY)
                if y2 in adjX[x] or len(adjY[y2]) >= d:
                    continue
                self._remove(x, y)
                self._add(x, y2)
                delta = self.U - before
                if delta > 0 and rng.random() >= math.exp(-delta / T):
                    self._remove(x, y2)
                    self._add(x, y)
                continue

            if r < 0.8:
                # Move the X-end of an edge at y to an X-vertex with spare degree.
                y = rng.randrange(nY)
                if not adjY[y]:
                    continue
                x = rng.choice(list(adjY[y]))
                x2 = rng.randrange(nX)
                if x2 in adjY[y] or len(adjX[x2]) >= d:
                    continue
                self._remove(x, y)
                self._add(x2, y)
                delta = self.U - before
                if delta > 0 and rng.random() >= math.exp(-delta / T):
                    self._remove(x2, y)
                    self._add(x, y)
                continue

            # Degree-preserving double-edge swap.
            x1 = rng.randrange(nX)
            x2 = rng.randrange(nX)
            if x1 == x2 or not adjX[x1] or not adjX[x2]:
                continue
            y1 = rng.choice(list(adjX[x1]))
            y2 = rng.choice(list(adjX[x2]))
            if y2 in adjX[x1] or y1 in adjX[x2]:
                continue
            self._remove(x1, y1)
            self._remove(x2, y2)
            self._add(x1, y2)
            self._add(x2, y1)
            delta = self.U - before
            if delta > 0 and rng.random() >= math.exp(-delta / T):
                self._remove(x1, y2)
                self._remove(x2, y1)
                self._add(x1, y1)
                self._add(x2, y2)

    def graph(self):
        """Return (n, edges): X vertices 0..nX-1, Y vertices nX..nX+nY-1."""
        nX = self.nX
        edges = [(x, nX + y) for x in range(nX) for y in self.adjX[x]]
        return nX + self.nY, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5 * time_limit, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Arc-extended projective plane base (diameter 3, valid for D >= 3).
    base = None
    arc_deadline = start + 0.25 * budget
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > arc_deadline:
            break
        cand = _arc_base(d, q, random.Random(seed * 7919 + q), arc_deadline)
        if base is None or cand[0] > base[0]:
            base = cand

    if base is not None:
        nX, nY, pairs = base
        consider(nX + nY, [(x, nX + y) for x, y in pairs])

        # Bold search: covering-based annealing with growing side sizes.
        if nX + nY < _moore3(d) and time.monotonic() < deadline:
            cs = _CoverSearch(d, random.Random(seed + 17), start)
            cs.init(nX, nY, pairs)
            cs.grow()
            while time.monotonic() < deadline:
                cs.anneal(deadline, 2.0, 0.1, 6)
                if cs.U != 0:
                    break
                n, e = cs.graph()
                consider(n, e)
                cs.grow()

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
