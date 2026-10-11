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
# Mutable graph with vertex removal/restoration and diameter-preserving growth.
#
# Growth rule (diameter D=4): a new vertex x on side X joined to a set S of
# spare-degree vertices on the opposite side keeps diameter <= 4 exactly when
# the union of R3(s) over s in S covers every alive vertex.
#
# Iterated local search (new): remove a few vertices whose deletion keeps the
# diameter <= 4 (checked exactly), regrow with fresh randomized covers, and
# accept the result if the order does not drop. This lets the graph escape
# the greedy plateau that single-pass extension gets stuck on.
# ----------------------------------------------------------------------------

NOISE = 0.25


class _G:
    def __init__(self, n, edges):
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

    def copy(self):
        g = _G.__new__(_G)
        g.adj = [set(a) for a in self.adj]
        g.color = list(self.color)
        g.alive = list(self.alive)
        return g

    def size(self):
        return sum(self.alive)

    def add_vertex(self, S, c):
        x = len(self.adj)
        self.adj.append(set(S))
        for s in S:
            self.adj[s].add(x)
        self.color.append(c)
        self.alive.append(True)

    def remove_vertex(self, x):
        nb = self.adj[x]
        for s in nb:
            self.adj[s].discard(x)
        self.adj[x] = set()
        self.alive[x] = False
        return nb

    def restore_vertex(self, x, nb):
        self.adj[x] = nb
        for s in nb:
            self.adj[s].add(x)
        self.alive[x] = True

    def full_mask(self):
        m = 0
        for v, a in enumerate(self.alive):
            if a:
                m |= 1 << v
        return m

    def ball(self, r):
        N = len(self.adj)
        reach = [1 << v for v in range(N)]
        for _ in range(r):
            new = []
            for v in range(N):
                x = reach[v]
                for u in self.adj[v]:
                    x |= reach[u]
                new.append(x)
            reach = new
        return reach

    def diameter_ok(self, D):
        full = self.full_mask()
        reach = self.ball(D)
        return all((reach[v] & full) == full
                   for v in range(len(self.adj)) if self.alive[v])

    def edges(self):
        ids = {}
        for v, a in enumerate(self.alive):
            if a:
                ids[v] = len(ids)
        E = [(ids[u], ids[v]) for u in range(len(self.adj)) if self.alive[u]
             for v in self.adj[u] if v > u]
        return len(ids), E


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


def _grow(g, d, deadline, rng, max_fails):
    """Add vertices greedily while keeping max degree d and diameter 4. Returns number added."""
    added = 0
    fails = 0
    while time.monotonic() < deadline:
        reach = g.ball(3)
        full = g.full_mask()
        grown = False
        while time.monotonic() < deadline:
            spare = [v for v in range(len(g.adj)) if g.alive[v] and len(g.adj[v]) < d]
            if not spare or fails >= max_fails:
                return added
            s0 = rng.choice(spare)
            pool = [v for v in spare if g.color[v] == g.color[s0] and v != s0]
            S = [s0]
            unc = full & ~reach[s0]
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
            g.add_vertex(S, 1 - g.color[s0])
            added += 1
            fails = 0
            grown = True
            break
        if not grown:
            return added
    return added


def _ils(g, d, deadline, rng, D):
    """Iterated local search: remove a few safe vertices, regrow, keep if order does not drop."""
    best = g
    bestn = g.size()
    while time.monotonic() < deadline:
        cur = best.copy()
        alive_ids = [v for v in range(len(cur.adj)) if cur.alive[v]]
        if not alive_ids:
            break
        target = rng.randint(1, 3)
        removed = 0
        for x in rng.sample(alive_ids, min(4, len(alive_ids))):
            if removed >= target:
                break
            nb = cur.remove_vertex(x)
            if cur.diameter_ok(D):
                removed += 1
            else:
                cur.restore_vertex(x, nb)
        if removed == 0:
            continue
        _grow(cur, d, deadline, rng, 200)
        if cur.size() >= bestn:
            best = cur
            bestn = cur.size()
    return best


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

    # Twin graph on W(d-2), then greedy growth and iterated local search.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        q = d - 2
        for attempt in range(2):
            now = time.monotonic()
            rem = deadline - now
            if rem < 3.0:
                break
            share = rem if attempt == 1 else rem * 0.5
            ils_dl = now + share
            try:
                n2, e2 = _twin_graph(q, now + share * 0.3, rng)
                g = _G(n2, e2)
                t1 = time.monotonic()
                _grow(g, d, t1 + (ils_dl - t1) * 0.3, rng, 3000)
                res = _ils(g, d, ils_dl, rng, D)
                consider(*res.edges())
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
