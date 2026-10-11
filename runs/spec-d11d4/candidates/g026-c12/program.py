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
    c = [0] * n
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
    padj = [set() for _ in range(P)]
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]
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
# Mutable bipartite graph with vertex-id reuse, used by the cover extension.
#
# Invariant: a vertex x of side X may join a set S of vertices on the opposite
# side if the union of their radius-3 balls covers all alive vertices. Then
# every pair involving x is within distance 4. Adding vertices never increases
# distances, so the existing pairs stay fine.
# ----------------------------------------------------------------------------

class _Graph:
    def __init__(self, n, edges, d):
        self.d = d
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
        self.free = []

    def alloc(self, c):
        if self.free:
            v = self.free.pop()
            self.alive[v] = True
            self.color[v] = c
            self.adj[v] = set()
            return v
        v = len(self.adj)
        self.adj.append(set())
        self.color.append(c)
        self.alive.append(True)
        return v

    def add_vertex(self, S, c):
        x = self.alloc(c)
        for s in S:
            self.adj[s].add(x)
            self.adj[x].add(s)
        return x

    def kill_vertex(self, x):
        for s in list(self.adj[x]):
            self.adj[s].discard(x)
        self.adj[x] = set()
        self.alive[x] = False
        self.free.append(x)

    def remove_vertex(self, x):
        nbrs = list(self.adj[x])
        for s in nbrs:
            self.adj[s].discard(x)
        self.adj[x] = set()
        self.alive[x] = False
        return nbrs

    def restore_vertex(self, x, nbrs):
        self.alive[x] = True
        for s in nbrs:
            self.adj[s].add(x)
            self.adj[x].add(s)

    def spare_list(self):
        return [v for v in range(len(self.adj)) if self.alive[v] and len(self.adj[v]) < self.d]

    def alive_mask(self):
        m = 0
        for v in range(len(self.adj)):
            if self.alive[v]:
                m |= 1 << v
        return m

    def ball3(self):
        N = len(self.adj)
        reach = [1 << v for v in range(N)]
        for _ in range(3):
            new = []
            for v in range(N):
                r = reach[v]
                for u in self.adj[v]:
                    r |= reach[u]
                new.append(r)
            reach = new
        return reach

    def export(self):
        ids = [v for v in range(len(self.adj)) if self.alive[v]]
        idx = {v: i for i, v in enumerate(ids)}
        edges = []
        for v in ids:
            for u in self.adj[v]:
                if u > v:
                    edges.append((idx[v], idx[u]))
        return len(ids), edges


NOISE = 0.25
MAX_FAILS = 20000
MAX_ADD = 4          # max vertices re-added after a removal in the swap phase
PLATEAU = 0.15       # probability of accepting a swap that keeps the order


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


def _cover_once(G, spare, reach, full, rng, tries):
    """Try to find a cover (S, colour) for a new vertex; return None if no cover was found."""
    if not spare:
        return None
    for _ in range(tries):
        s0 = rng.choice(spare)
        pool = [v for v in spare if G.color[v] == G.color[s0] and v != s0]
        S = [s0]
        unc = full & ~reach[s0]
        while unc and len(S) < G.d and pool:
            bv = _pick(pool, reach, unc, rng)
            if bv < 0:
                break
            S.append(bv)
            unc &= ~reach[bv]
            pool.remove(bv)
        if not unc:
            return S, 1 - G.color[s0]
    return None


def _extend(G, rng, deadline):
    """Greedy randomized cover extension until saturation or deadline."""
    while time.monotonic() < deadline:
        spare = G.spare_list()
        if not spare:
            return
        reach = G.ball3()
        full = G.alive_mask()
        fails = 0
        placed = False
        while time.monotonic() < deadline and fails < MAX_FAILS:
            r = _cover_once(G, spare, reach, full, rng, 1)
            if r is None:
                fails += 1
                continue
            S, c = r
            G.add_vertex(S, c)
            placed = True
            break
        if not placed:
            return


def _swap(G, base_n, rng, deadline, d, D):
    """Local search: remove one extension vertex, refill with up to MAX_ADD vertices, keep if valid and not smaller."""
    while time.monotonic() < deadline:
        cands = [v for v in range(len(G.adj)) if G.alive[v] and v >= base_n]
        if not cands:
            return
        x = rng.choice(cands)
        nbrs = G.remove_vertex(x)
        added = []
        while len(added) < MAX_ADD and time.monotonic() < deadline:
            reach = G.ball3()
            full = G.alive_mask()
            spare = G.spare_list()
            r = _cover_once(G, spare, reach, full, rng, 30)
            if r is None:
                break
            S, c = r
            added.append(G.add_vertex(S, c))
        gain = len(added) - 1
        ok = False
        if gain >= 1 or (gain == 0 and rng.random() < PLATEAU):
            m, edges = G.export()
            ok = lib.is_valid(m, edges, d, D)
        if ok:
            G.free.append(x)
        else:
            for a in reversed(added):
                G.kill_vertex(a)
            G.restore_vertex(x, nbrs)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
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

    # Twin graph on W(d-2), cover extension, then swap-based local search.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, t0 + 0.4 * budget, rng)
            consider(n2, e2)
            G = _Graph(n2, e2, d)
            _extend(G, rng, t0 + 0.55 * budget)
            n3, e3 = G.export()
            consider(n3, e3)
            _swap(G, n2, rng, deadline, d, D)
            n4, e4 = G.export()
            consider(n4, e4)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
