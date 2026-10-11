import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Diameter-3 extension rule for bipartite graphs (new in this version).
#
# In a bipartite graph with sides A (side 0) and B (side 1), if a new vertex x
# on side A has neighbourhood N (a subset of B), then every existing vertex is
# within distance 3 of x exactly when
#   (i)  every existing A-vertex has a neighbour in N  (distance 2), and
#   (ii) every existing B-vertex has at least one neighbour (true by construction).
# Adding vertices never increases distances among old vertices, so insertion
# only needs this covering test. The test is an exact set-cover problem: cover
# the A-side by B-vertices with spare degree, using at most d of them.
#
# _find_cover solves it by depth-first search that branches on the most
# constrained uncovered vertex, with a node budget. Stars (pencils of a
# projective plane) are the natural solutions, and the search also finds
# non-star covers that the stars alone miss.
#
# _ils then runs an iterated local search: remove a few added vertices, regrow
# with the cover search, and accept only graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------


class _Graph:
    """Bipartite graph kept as adjacency sets. side 0 = A, side 1 = B."""

    def __init__(self, d):
        self.d = d
        self.adj = {}
        self.side = {}
        self.added = set()
        self.next_id = 0

    def add_vertex(self, side, extra=True):
        v = self.next_id
        self.next_id += 1
        self.adj[v] = set()
        self.side[v] = side
        if extra:
            self.added.add(v)
        return v

    def link(self, u, v):
        self.adj[u].add(v)
        self.adj[v].add(u)

    def remove(self, v):
        """Remove an added vertex; added neighbours left isolated are removed too."""
        stack = [v]
        while stack:
            x = stack.pop()
            if x not in self.adj:
                continue
            nbrs = self.adj.pop(x)
            del self.side[x]
            self.added.discard(x)
            for u in nbrs:
                self.adj[u].discard(x)
                if not self.adj[u] and u in self.added:
                    stack.append(u)

    def edges(self):
        return [(u, v) for u in self.adj for v in self.adj[u] if u < v]

    def snapshot(self):
        return ({v: set(s) for v, s in self.adj.items()}, dict(self.side), set(self.added))

    def restore(self, snap):
        adj, side, added = snap
        self.adj = {v: set(s) for v, s in adj.items()}
        self.side = dict(side)
        self.added = set(added)


def _find_cover(G, side, rng, node_limit):
    """Find N on the opposite side (degree < d each), |N| <= d, covering every vertex of `side`.

    Returns the list N, or None. Uses DFS branching on the uncovered vertex with
    the fewest spare options.
    """
    d = G.d
    adj = G.adj
    cands = [len(adj[b]) for b in adj if G.side[b] != side and len(adj[b]) < d]
    if not cands:
        return None
    maxcov = max(cands)
    U = [v for v in adj if G.side[v] == side]
    if not U:
        return None
    cnt = {u: 0 for u in U}
    for b in adj:
        if G.side[b] != side and len(adj[b]) < d:
            for u in adj[b]:
                cnt[u] += 1
    uncovered = set(U)
    chosen = []
    chosen_set = set()
    nodes = [0]

    def dfs():
        if not uncovered:
            return True
        r = d - len(chosen)
        if r <= 0 or len(uncovered) > r * maxcov:
            return False
        nodes[0] += 1
        if nodes[0] > node_limit:
            return False
        bu, bc = None, None
        for u in uncovered:
            c = cnt[u]
            if bc is None or c < bc:
                bu, bc = u, c
                if c <= 1:
                    break
        if bc == 0:
            return False
        opts = [b for b in adj[bu] if b not in chosen_set and len(adj[b]) < d]
        rng.shuffle(opts)
        for b in opts:
            hit = [w for w in adj[b] if w in uncovered]
            chosen.append(b)
            chosen_set.add(b)
            for w in adj[b]:
                cnt[w] -= 1
            for w in hit:
                uncovered.discard(w)
            if dfs():
                return True
            for w in hit:
                uncovered.add(w)
            for w in adj[b]:
                cnt[w] += 1
            chosen.pop()
            chosen_set.discard(b)
            if nodes[0] > node_limit:
                return False
        return False

    if dfs():
        return list(chosen)
    return None


def _grow(G, rng, deadline, node_limit):
    """Repeatedly add vertices (both sides, random order) while covers are found."""
    while time.monotonic() < deadline:
        grew = False
        sides = [0, 1]
        rng.shuffle(sides)
        for side in sides:
            cover = _find_cover(G, side, rng, node_limit)
            if cover is None:
                continue
            x = G.add_vertex(side)
            for b in cover:
                G.link(x, b)
            grew = True
        if not grew:
            break


def _ils(G, rng, deadline, d, D, best, node_limit):
    """Iterated local search: remove a few added vertices, regrow, keep valid results."""
    cur = len(G.adj)
    T = 0.6
    while time.monotonic() < deadline and G.added:
        snap = G.snapshot()
        k = rng.choice((1, 1, 2, 2, 3))
        pool = list(G.added)
        for _ in range(k):
            if not pool:
                break
            v = pool.pop(rng.randrange(len(pool)))
            G.remove(v)
        _grow(G, rng, deadline, node_limit)
        new = len(G.adj)
        if new < cur and rng.random() >= math.exp((new - cur) / T):
            G.restore(snap)
            continue
        n, E = lib.relabel(G.edges())
        if not lib.is_valid(n, E, d, D):
            G.restore(snap)
            continue
        cur = new
        if n > best[0]:
            best = (n, E)
    return best


# ----------------------------------------------------------------------------
# Projective-plane bases and star initialisations (diameter 3).
# ----------------------------------------------------------------------------

def _pg(q):
    """Return (m, edges, pl, lp): points 0..m-1, lines m..2m-1; pl[P] = lines through P, lp[L] = points on L."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _base_graph(d, m, edges):
    G = _Graph(d)
    for i in range(2 * m):
        G.add_vertex(0 if i < m else 1, extra=False)
    for u, v in edges:
        G.link(u, v)
    return G


def _star_a(G, m, pl, P):
    """New A-vertex joined to the lines through point P (a pencil). Needs spare on those lines."""
    lines = [m + L for L in pl[P]]
    if any(len(G.adj[b]) >= G.d for b in lines):
        return False
    x = G.add_vertex(0)
    for b in lines:
        G.link(x, b)
    return True


def _star_b(G, lp, L):
    """New B-vertex joined to the points on line L. Needs spare on those points."""
    pts = lp[L]
    if any(len(G.adj[Q]) >= G.d for Q in pts):
        return False
    y = G.add_vertex(1)
    for Q in pts:
        G.link(y, Q)
    return True


def _star_init(G, m, pl, lp, rng):
    pa = list(range(m))
    pb = list(range(m))
    rng.shuffle(pa)
    rng.shuffle(pb)
    for P, L in zip(pa, pb):
        _star_a(G, m, pl, P)
        _star_b(G, lp, L)


def _conic_init(G, q, d, m, pl, lp):
    """Parent-style conic arc extension; valid when all line and point loads stay within spare s = d-q-1."""
    s = d - q - 1
    if s < 2:
        return False
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    if max(cl) > s or max(cp) > s:
        return False
    for P in S:
        _star_a(G, m, pl, P)
    for j in S:
        _star_b(G, lp, j)
    return True


def _search_d3(d, deadline, rng):
    """Search for D = 3 graphs over the largest few prime-power bases with q + 1 <= d."""
    qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
    best = (0, [])
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(qs) - idx)
        m, edges, pl, lp = _pg(q)
        starts = []
        G1 = _base_graph(d, m, edges)
        _star_init(G1, m, pl, lp, rng)
        starts.append(G1)
        G2 = _base_graph(d, m, edges)
        if _conic_init(G2, q, d, m, pl, lp):
            starts.append(G2)
        for G in starts:
            _grow(G, rng, end, 400)
        G = max(starts, key=lambda g: len(g.adj))
        n, E = lib.relabel(G.edges())
        if n > best[0] and lib.is_valid(n, E, d, 3):
            best = (n, E)
        best = _ils(G, rng, end, d, 3, best, 200)
    return best


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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    if D == 3:
        cand = _search_d3(d, deadline, rng)
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    elif D >= 4:
        gq = _best_gq(d)
        if gq is not None and gq[0] > best[0] and lib.is_valid(gq[0], gq[1], d, D):
            best = gq

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
