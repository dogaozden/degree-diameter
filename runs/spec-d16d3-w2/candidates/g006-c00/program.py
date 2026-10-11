import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane start (diameter 3).
#
# Incidence graph of PG(2, q) plus, for each P in an arc S, a new "A" vertex
# joined to the q+1 lines through P, and for each j in S a new "B" vertex joined
# to the q+1 points on line j. Each old vertex gains at most s = d-q-1 extra
# edges, so S must load every line and point at most s times.
# ----------------------------------------------------------------------------

def _pg_struct(q):
    """Return (m, edges, pl, lp, index) for PG(2, q); points are 0..m-1, lines m..2m-1."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]   # lines through point P
    lp = [[] for _ in range(m)]   # points on line L
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, pl, lp, index


def _loads_ok(S, s, m, pl, lp):
    """True if every line and point receives at most s extra edges from S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, trials, deadline):
    """Randomized greedy arc respecting the load bound s."""
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
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index):
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_start(d, rng, deadline):
    """Best arc-extended graph over prime powers q with q + 1 <= d. Returns (n, E, m, pl, lp) or None."""
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index = _pg_struct(q)
        S = _greedy_arc(m, s, pl, lp, rng, 30, deadline) if s >= 1 else []
        if s >= 2:
            cs = _conic_set(q, index)
            if len(cs) > len(S) and _loads_ok(cs, s, m, pl, lp):
                S = cs
        if not _loads_ok(S, s, m, pl, lp):
            continue
        n = 2 * m + 2 * len(S)
        if best is None or n > best[0]:
            best = (n, m, edges, pl, lp, S)
    if best is None:
        return None
    n, m, edges, pl, lp, S = best
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        for L in pl[P]:
            E.append((2 * m + t, m + L))
    for t, j in enumerate(S):
        for Q in lp[j]:
            E.append((Q, 2 * m + k + t))
    return n, E, m, pl, lp


# ----------------------------------------------------------------------------
# NEW: journaled edge-swap plateau search.
#
# Moves on a valid graph:
#   grow  - add a vertex adjacent to the spare-capacity neighbours of a pencil
#           (points -> lines through an anchor point) or dual star (lines -> points
#           of an anchor line); the best of several random anchors is used;
#   swap  - delete a random edge (freeing two slots), then try to grow;
#   shrink- delete all edges of a random added vertex.
# Each move is journaled and undone unless lib.is_valid still holds and the
# vertex count does not drop (with a Metropolis allowance for drops).
# Edge swaps let the walk move across a plateau of equal-size valid graphs.
# ----------------------------------------------------------------------------

class _Search:
    def __init__(self, d, D, E0, base, m, pl, lp, rng):
        self.d = d
        self.D = D
        self.base = base
        self.m = m
        self.pl = pl
        self.lp = lp
        self.rng = rng
        self.adj = {}
        self.log = []
        for u, v in E0:
            self._raw_add(u, v)
        self.nxt = max(max(e) for e in E0) + 1

    def _raw_add(self, u, v):
        self.adj.setdefault(u, set()).add(v)
        self.adj.setdefault(v, set()).add(u)

    def _raw_del(self, u, v):
        s = self.adj[u]
        s.discard(v)
        if not s:
            del self.adj[u]
        t = self.adj[v]
        t.discard(u)
        if not t:
            del self.adj[v]

    def _add(self, u, v):
        self._raw_add(u, v)
        self.log.append((1, u, v))

    def _del(self, u, v):
        self._raw_del(u, v)
        self.log.append((0, u, v))

    def _undo(self):
        while self.log:
            op, u, v = self.log.pop()
            if op == 1:
                self._raw_del(u, v)
            else:
                self._raw_add(u, v)

    def deg(self, v):
        s = self.adj.get(v)
        return len(s) if s else 0

    def edges(self):
        return [(u, v) for u, s in self.adj.items() for v in s if u < v]

    def nverts(self):
        return len(self.adj)

    def valid(self):
        n, E = lib.relabel(self.edges())
        return lib.is_valid(n, E, self.d, self.D)

    def _grow(self):
        rng, m, d = self.rng, self.m, self.d
        best = None
        for _ in range(24):
            if rng.random() < 0.5:
                R = rng.randrange(m)
                nb = [m + L for L in self.pl[R] if self.deg(m + L) < d]
            else:
                j = rng.randrange(m)
                nb = [Q for Q in self.lp[j] if self.deg(Q) < d]
            if len(nb) >= 2 and (best is None or len(nb) > len(best)):
                best = nb
        if best is None:
            return False
        x = self.nxt
        self.nxt += 1
        for u in best:
            self._add(x, u)
        return True

    def _swap(self):
        E = self.edges()
        if not E:
            return False
        u, v = self.rng.choice(E)
        self._del(u, v)
        self._grow()
        return True

    def _shrink(self):
        news = [v for v in self.adj if v >= self.base]
        if not news:
            return False
        x = self.rng.choice(news)
        for u in list(self.adj[x]):
            self._del(x, u)
        return True

    def run(self, deadline, T=0.5):
        cur = self.nverts()
        best = cur
        best_E = self.edges()
        rng = self.rng
        while time.monotonic() < deadline:
            self.log = []
            r = rng.random()
            if r < 0.55:
                changed = self._grow()
            elif r < 0.92:
                changed = self._swap()
            else:
                changed = self._shrink()
            if not changed:
                continue
            if not self.valid():
                self._undo()
                continue
            new = self.nverts()
            if new >= cur or rng.random() < math.exp((new - cur) / T):
                cur = new
                if cur > best:
                    best = cur
                    best_E = self.edges()
            else:
                self._undo()
        return best, best_E


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        N = 2 * D
        return N, [(i, (i + 1) % N) for i in range(N)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        cand = _arc_start(d, rng, start + 0.2 * time_limit)
        if cand is not None:
            n, E, m, pl, lp = cand
            if n > best[0] and lib.is_valid(n, E, d, D):
                best = (n, E)

            deg = {}
            for u, v in E:
                deg[u] = deg.get(u, 0) + 1
                deg[v] = deg.get(v, 0) + 1
            spare = sum(d - c for c in deg.values())
            if spare > 0 and n == best[0] and time.monotonic() < deadline:
                srch = _Search(d, D, E, 2 * m, m, pl, lp, random.Random(seed * 131 + 17))
                cnt, bE = srch.run(deadline)
                n2, E2 = lib.relabel(bE)
                if n2 > best[0] and lib.is_valid(n2, E2, d, D):
                    best = (n2, E2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
