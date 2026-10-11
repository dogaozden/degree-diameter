import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as a point/line list (table-based, pure Python).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Return (P, lines): points of W(q) indexed 0..P-1 and each totally isotropic line as a sorted point list."""
    F = lib.GF(q)
    mul = F.mul_table.tolist()
    add = F.add_table.tolist()
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if mul[a][b] == 1)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        ic = inv[c]
        return tuple(mul[ic][x] for x in v)

    def form(x, y):
        t = add[mul[x[0]][y[1]]][neg[mul[x[1]][y[0]]]]
        u = add[mul[x[2]][y[3]]][neg[mul[x[3]][y[2]]]]
        return add[t][u]

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i * P + j) in covered:
                continue
            y = pts[j]
            if form(x, y):
                continue
            Lset = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(add[mul[a][x[k]]][mul[b][y[k]]] for k in range(4))
                    if any(v):
                        Lset.add(index[norm(v)])
            Ls = sorted(Lset)
            lines.append(Ls)
            for p in Ls:
                for r in Ls:
                    if p < r:
                        covered.add(p * P + r)
    return P, lines


def _gq_incidence(q):
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    P, lines = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Maximum independent set by k-fixed tabu search (pure Python).
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    inS = [False] * n
    c = [0] * n          # number of neighbours of v inside S
    S = []

    def add(v):
        inS[v] = True
        S.append(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.remove(u)
        for w in adj[u]:
            c[w] -= 1

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if c[v] == 0:
            add(v)
    best = list(S)
    tab_add = [0] * n
    tab_rem = [0] * n
    it = 0
    stuck = 0
    while time.monotonic() < deadline:
        it += 1
        cost = sum(c[v] for v in S)
        if cost == 0:
            if len(S) > len(best):
                best = list(S)
                stuck = 0
            cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
                or [v for v in range(n) if not inS[v]]
            if not cands:
                break
            mn = min(c[v] for v in cands)
            add(rng.choice([v for v in cands if c[v] == mn]))
            continue
        stuck += 1
        if stuck > 3000:
            # Restart from the best independent set found so far.
            for v in list(S):
                remove(v)
            for v in best:
                add(v)
            stuck = 0
            continue
        ok = [u for u in S if tab_rem[u] <= it] or list(S)
        mx = max(c[u] for u in ok)
        u = rng.choice([x for x in ok if c[x] == mx])
        remove(u)
        tab_add[u] = it + rng.randint(5, 15)
        cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
            or [v for v in range(n) if not inS[v]]
        mn = min(c[v] for v in cands)
        v = rng.choice([x for x in cands if c[x] == mn])
        add(v)
        tab_rem[v] = it + rng.randint(5, 15)
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    P, lines = _gq_w(q)
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    padj = [set() for _ in range(P)]          # collinear points
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]          # lines sharing a point
    for p in range(P):
        for a in pl[p]:
            for b in pl[p]:
                if a != b:
                    ladj[a].add(b)

    now = time.monotonic()
    mid = now + (deadline - now) / 2.0
    I = _mis(P, [sorted(s) for s in padj], mid, rng)
    J = _mis(L, [sorted(s) for s in ladj], deadline, rng)

    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        n += 1
    return n, edges


# ----------------------------------------------------------------------------
# Set-cover extension for diameter 4, with iterated local search.
#
# Let R3(v) be the set of vertices within distance 3 of v. A new vertex x on
# side X, joined to a set S of spare-degree vertices on the opposite side Y,
# keeps diameter <= 4 exactly when the union of R3(s) over s in S covers every
# live vertex. Adding x only shortens distances, so no other pair can break.
#
# Change in this version: after the greedy extension saturates, an iterated
# local search takes over. It deletes one random added vertex (freeing its
# d slots in its neighbours), regrows greedily into the freed space, and keeps
# the result if the vertex count did not drop, otherwise it undoes the move
# from a log. This lets the search cross plateaus that pure greedy cannot.
# Vertices are never renumbered during the search; deleted ids are recycled
# through a free list, and the best graph is compacted at the end.
# ----------------------------------------------------------------------------

NOISE = 0.25


def _ball3(n, adj):
    """Return per-vertex bitmasks of all vertices within distance 3."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _pick(pool, reach, unc, rng):
    """Choose the next cover vertex from pool: best gain, or a random useful one with prob NOISE."""
    if rng.random() < NOISE:
        useful = [v for v in pool if reach[v] & unc]
        if useful:
            return rng.choice(useful)
        return -1
    best, bv = 0, -1
    for v in pool:
        g = (reach[v] & unc).bit_count()
        if g > best:
            best, bv = g, v
    return bv


class _Ext:
    """Mutable extension state: live mask, adjacency sets, colours, and a free list of deleted ids."""

    def __init__(self, n, edges, d):
        self.d = d
        self.base = n
        self.adj = [set() for _ in range(n)]
        for u, v in edges:
            self.adj[u].add(v)
            self.adj[v].add(u)
        self.color = [-1] * n
        for s in range(n):
            if self.color[s] != -1:
                continue
            self.color[s] = 0
            stack = [s]
            while stack:
                u = stack.pop()
                for w in self.adj[u]:
                    if self.color[w] == -1:
                        self.color[w] = 1 - self.color[u]
                        stack.append(w)
        self.alive = [True] * n
        self.amask = (1 << n) - 1
        self.free = []
        self.count = n
        self.reach = None
        self.spare = None

    def _add(self, S, c):
        if self.free:
            x = self.free.pop()
            self.adj[x] = set(S)
            self.alive[x] = True
            self.color[x] = c
        else:
            x = len(self.adj)
            self.adj.append(set(S))
            self.alive.append(True)
            self.color.append(c)
        for s in S:
            self.adj[s].add(x)
        self.amask |= 1 << x
        self.count += 1
        self.reach = None
        self.spare = None
        return x

    def _remove(self, x):
        nb = list(self.adj[x])
        for s in nb:
            self.adj[s].discard(x)
        self.adj[x] = set()
        self.alive[x] = False
        self.amask &= ~(1 << x)
        self.count -= 1
        self.free.append(x)
        self.reach = None
        self.spare = None
        return nb

    def _restore(self, x, nb):
        self.free.remove(x)
        self.adj[x] = set(nb)
        self.alive[x] = True
        for s in nb:
            self.adj[s].add(x)
        self.amask |= 1 << x
        self.count += 1
        self.reach = None
        self.spare = None

    def grow(self, max_fails, deadline, log, rng):
        """Greedily add cover vertices until max_fails consecutive attempts fail or no spare degree remains."""
        d = self.d
        fails = 0
        while fails < max_fails and time.monotonic() < deadline:
            if self.reach is None:
                self.reach = _ball3(len(self.adj), self.adj)
            if self.spare is None:
                self.spare = [v for v in range(len(self.adj))
                              if self.alive[v] and len(self.adj[v]) < d]
            spare = self.spare
            if not spare:
                return
            reach = self.reach
            color = self.color
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = self.amask & ~reach[s0]
            while unc and len(S) < d and pool:
                bv = _pick(pool, reach, unc, rng)
                if bv < 0:
                    break
                S.append(bv)
                unc &= ~reach[bv]
                pool.remove(bv)
            if unc:
                fails += 1
                continue
            x = self._add(S, 1 - color[s0])
            log.append(('add', x))
            fails = 0

    def undo(self, log):
        for item in reversed(log):
            if item[0] == 'add':
                self._remove(item[1])
            else:
                self._restore(item[1], item[2])
        self.reach = None
        self.spare = None

    def snapshot(self):
        return [(v, w) for v in range(len(self.adj)) if self.alive[v]
                for w in self.adj[v] if w > v]

    def run(self, deadline, rng):
        """Greedy saturation, then remove-and-regrow local search. Returns the best (n, edges) found."""
        self.grow(20000, deadline, [], rng)
        best_count = self.count
        best = self.snapshot()
        while time.monotonic() < deadline:
            cand = [v for v in range(self.base, len(self.adj)) if self.alive[v]]
            if not cand:
                break
            before = self.count
            log = []
            x = rng.choice(cand)
            log.append(('rem', x, self._remove(x)))
            self.grow(300, deadline, log, rng)
            if self.count < before:
                self.undo(log)
            elif self.count > best_count:
                best_count = self.count
                best = self.snapshot()
        return lib.relabel(best)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    twin_deadline = t0 + 0.5 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    # Projective plane incidence graph: degree d, diameter 3.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Twin graph on W(d-2), then local-search set-cover extension using spare slots.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            ext = _Ext(n2, e2, d)
            n3, e3 = ext.run(deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
