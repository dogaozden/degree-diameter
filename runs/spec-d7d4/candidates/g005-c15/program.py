import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
#   D = 3: incidence graph of PG(2, q).
#   D >= 4: incidence graph of the generalized quadrangle W(q).
#   otherwise: K_{d,d}, which is always valid for D >= 2.
# Every base lists its side-0 vertices first, so colour = (index >= n/2).
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


def _base(d, D):
    if D == 3:
        for q in range(min(d - 1, 23), 1, -1):
            if lib.is_prime_power(q):
                return lib.projective_plane_incidence(q)
        return None
    if D >= 4:
        for q in range(min(d - 1, 9), 1, -1):
            if lib.is_prime_power(q):
                return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Mutable bipartite graph state. Edges are stored as (side0, side1) pairs.
# ----------------------------------------------------------------------------

class _G:
    def __init__(self, n, edges, col):
        self.n = n
        self.col = list(col)
        self.deg = [0] * n
        self.E = []
        self.Es = set()
        for u, v in edges:
            a, b = (u, v) if self.col[u] == 0 else (v, u)
            self._add_edge(a, b)

    def _add_edge(self, a, b):
        self.E.append((a, b))
        self.Es.add((a, b))
        self.deg[a] += 1
        self.deg[b] += 1

    def copy(self):
        g = _G.__new__(_G)
        g.n = self.n
        g.col = list(self.col)
        g.deg = list(self.deg)
        g.E = list(self.E)
        g.Es = set(self.Es)
        return g

    def adj(self):
        adj = [[] for _ in range(self.n)]
        for a, b in self.E:
            adj[a].append(b)
            adj[b].append(a)
        return adj

    def add_vertex(self, c, nbrs):
        v = self.n
        self.n += 1
        self.col.append(c)
        self.deg.append(0)
        for s in nbrs:
            if c == 0:
                self._add_edge(v, s)
            else:
                self._add_edge(s, v)

    def cost(self, D):
        return lib.bad_pairs(self.n, self.E, D)


def _balls(n, adj, r):
    """Bitmask of the radius-r ball around every vertex."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        nxt = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt[v] = x
        ball = nxt
    return ball


# ----------------------------------------------------------------------------
# Exact growth: a new vertex is added only if its neighbours' radius-(D-1)
# balls cover every vertex. Diameter is preserved with no repair.
# ----------------------------------------------------------------------------

def _cover(ball, cands, full, d, rng, budget):
    """Bounded DFS for <= d candidates whose balls cover `full`; returns a list or None."""
    used = set()
    chosen = []
    nodes = [0]

    def rec(covered, depth):
        if covered == full:
            return True
        if depth >= d or nodes[0] >= budget:
            return False
        nodes[0] += 1
        rem = full & ~covered
        free = [s for s in cands if s not in used]
        gains = {s: (ball[s] & rem).bit_count() for s in free}
        best = max(gains.values(), default=0)
        if best == 0 or rem.bit_count() > best * (d - depth):
            return False
        bits = []
        x = rem
        while x:
            low = x & -x
            bits.append(low.bit_length() - 1)
            x ^= low
        sample = rng.sample(bits, min(6, len(bits)))
        best_opts = None
        for w in sample:
            opts = [s for s in free if gains[s] and (ball[s] >> w) & 1]
            if best_opts is None or len(opts) < len(best_opts):
                best_opts = opts
        if not best_opts:
            return False
        rng.shuffle(best_opts)
        best_opts.sort(key=lambda s: -gains[s])
        for s in best_opts:
            used.add(s)
            chosen.append(s)
            if rec(covered | ball[s], depth + 1):
                return True
            used.discard(s)
            chosen.pop()
            if nodes[0] >= budget:
                break
        return False

    return list(chosen) if rec(0, 0) else None


def _try_exact(g, d, D, rng, budget):
    ball = _balls(g.n, g.adj(), D - 1)
    full = (1 << g.n) - 1
    sides = [0, 1]
    rng.shuffle(sides)
    for c in sides:
        cands = [s for s in range(g.n) if g.col[s] == 1 - c and g.deg[s] < d]
        if not cands:
            continue
        chosen = _cover(ball, cands, full, d, rng, budget)
        if chosen:
            g.add_vertex(c, chosen)
            return True
    return False


def _saturate(g, d, rng):
    """Add edges between spare-degree vertices on opposite sides. Never breaks diameter."""
    left = [v for v in range(g.n) if g.col[v] == 0 and g.deg[v] < d]
    right = [v for v in range(g.n) if g.col[v] == 1 and g.deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (a, b) not in g.Es]
    rng.shuffle(pairs)
    added = 0
    for a, b in pairs:
        if g.deg[a] < d and g.deg[b] < d:
            g._add_edge(a, b)
            added += 1
    return added


def _grow_exact(g, d, D, rng, deadline):
    while time.monotonic() < deadline:
        if _try_exact(g, d, D, rng, 800):
            continue
        if _saturate(g, d, rng) == 0:
            break
    return g


# ----------------------------------------------------------------------------
# Repair search: add a vertex with a best-effort neighbourhood, then anneal
# degree-preserving double-edge swaps (plus edge insertions) until the graph
# has diameter <= D again. Cost = number of pairs at distance > D.
# ----------------------------------------------------------------------------

def _repair(g, d, D, deadline, rng):
    cost = g.cost(D)
    if cost == 0:
        return True
    E, Es, deg, col = g.E, g.Es, g.deg, g.col
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return False
        T = 0.05 + 2.0 * (1.0 - (now - start) / span)
        if rng.random() < 0.15:
            L = [s for s in range(g.n) if col[s] == 0 and deg[s] < d]
            R = [s for s in range(g.n) if col[s] == 1 and deg[s] < d]
            if L and R:
                a = rng.choice(L)
                b = rng.choice(R)
                if (a, b) not in Es:
                    E.append((a, b))
                    Es.add((a, b))
                    deg[a] += 1
                    deg[b] += 1
                    cost = g.cost(D)
            continue
        m = len(E)
        i = rng.randrange(m)
        j = rng.randrange(m)
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or (a, e) in Es or (c, b) in Es:
            continue
        E[i] = (a, e)
        E[j] = (c, b)
        c2 = g.cost(D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            Es.discard((a, b))
            Es.discard((c, e))
            Es.add((a, e))
            Es.add((c, b))
            cost = c2
        else:
            E[i] = (a, b)
            E[j] = (c, e)
    return True


def _grow_repair(g, d, D, deadline, rng):
    while time.monotonic() < deadline:
        sides = [0, 1]
        rng.shuffle(sides)
        c = None
        for cc in sides:
            if any(g.col[s] == 1 - cc and g.deg[s] < d for s in range(g.n)):
                c = cc
                break
        if c is None:
            break
        h = g.copy()
        ball = _balls(h.n, h.adj(), D - 1)
        full = (1 << h.n) - 1
        pool = [s for s in range(h.n) if h.col[s] == 1 - c and h.deg[s] < d]
        rng.shuffle(pool)
        chosen = []
        covered = 0
        while len(chosen) < d and pool:
            gains = [(ball[s] & ~covered).bit_count() for s in pool]
            i = max(range(len(pool)), key=lambda t: (gains[t], rng.random()))
            s = pool.pop(i)
            chosen.append(s)
            covered |= ball[s]
            if covered == full:
                break
        h.add_vertex(c, chosen)
        if _repair(h, d, D, min(deadline, time.monotonic() + 3.0), rng):
            g = h
    return g


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2
    base = _base(d, D)
    if base is None or not lib.is_valid(base[0], base[1], d, D):
        base = fallback
    base_n, base_e = base

    # Already at the Moore bound: nothing to search for.
    if base_n >= lib._moore_bound(d, D):
        return base_n, list(base_e)

    half = base_n // 2
    g = _G(base_n, base_e, [0] * half + [1] * half)
    _grow_exact(g, d, D, rng, deadline)
    g = _grow_repair(g, d, D, deadline, rng)

    if g.n >= base_n and lib.is_valid(g.n, g.E, d, D):
        return g.n, list(g.E)
    return base_n, list(base_e)
