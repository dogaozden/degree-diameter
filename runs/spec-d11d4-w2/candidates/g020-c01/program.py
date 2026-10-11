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


def _twin_graph(q, deadline, rng):
    """Twin construction on W(q): base for degree q+2, diameter 4."""
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
# Cover-based vertex extension, diameter 4.
#
# A new vertex x joined to a set S (all on one colour class, spare degree)
# keeps diameter <= 4 exactly when the union of ball3(s) over s in S covers
# every existing vertex.
#
# NEW IDEA: prefix-stack iterated local search. The extension vertices form a
# sequence where each prefix is itself a valid graph (diameter <= 4, degree <=
# d). So we can undo the last k extensions in O(k*d) and regrow with fresh
# randomness and noise. Improvements are kept, slight drops are sometimes
# accepted, and the best prefix-sequence is replayed at the end.
# ----------------------------------------------------------------------------

def _bfs_color(n, edges):
    """2-colour a bipartite graph given by edge list (colour 0/1 per vertex)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)
    return color


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


def _pick(pool, reach, unc, rng, noise):
    """Choose the next cover vertex from pool: best gain, or a random useful one with prob noise."""
    if rng.random() < noise:
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
    """Base graph plus a stack of extension vertices; supports O(d) undo of the last extension."""

    def __init__(self, n, edges):
        self.n = n
        self.edges = list(edges)
        self.adj = [[] for _ in range(n)]
        for u, v in self.edges:
            self.adj[u].append(v)
            self.adj[v].append(u)
        self.color = _bfs_color(n, self.edges)
        self.ext = []

    def add(self, S):
        c = self.color[S[0]]
        x = self.n
        self.n += 1
        for s in S:
            self.edges.append((s, x))
            self.adj[s].append(x)
        self.adj.append(list(S))
        self.color.append(1 - c)
        self.ext.append(tuple(S))

    def undo(self):
        S = self.ext.pop()
        for s in S:
            self.adj[s].pop()
        del self.edges[-len(S):]
        self.adj.pop()
        self.color.pop()
        self.n -= 1

    def reset_to(self, seq):
        while self.ext:
            self.undo()
        for S in seq:
            self.add(list(S))

    def grow(self, d, deadline, rng, noise, max_fails):
        fails = 0
        reach = None
        full = 0
        spare = []
        while fails < max_fails and time.monotonic() < deadline:
            if reach is None:
                reach = _ball3(self.n, self.adj)
                full = (1 << self.n) - 1
                spare = [v for v in range(self.n) if len(self.adj[v]) < d]
                if not spare:
                    return
            s0 = rng.choice(spare)
            pool = [v for v in spare if self.color[v] == self.color[s0] and v != s0]
            S = [s0]
            unc = full & ~reach[s0]
            while unc and len(S) < d and pool:
                bv = _pick(pool, reach, unc, rng, noise)
                if bv < 0:
                    break
                S.append(bv)
                unc &= ~reach[bv]
                pool.remove(bv)
            if unc:
                fails += 1
                continue
            self.add(S)
            reach = None
            fails = 0


def _ils(base_n, base_edges, d, deadline, rng):
    """Iterated local search over the extension stack; returns (n, edges)."""
    st = _Ext(base_n, base_edges)
    st.grow(d, deadline, rng, 0.1, 20000)
    cur = list(st.ext)
    best = list(cur)
    while time.monotonic() < deadline - 0.2:
        L = len(cur)
        if L > 0:
            k = rng.randint(1, min(L, 6))
            for _ in range(k):
                st.undo()
        noise = rng.choice([0.05, 0.1, 0.25, 0.4])
        st.grow(d, deadline, rng, noise, 300)
        new = list(st.ext)
        tol = 1 if rng.random() < 0.2 else 0
        if len(new) >= L - tol:
            cur = new
        else:
            st.reset_to(cur)
        if len(cur) > len(best):
            best = list(cur)
    st.reset_to(best)
    return st.n, list(st.edges)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
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
    if D == 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    if D >= 4:
        base = None
        # Twin graph on W(d-2): degree d, diameter 4, then iterated extension.
        if lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
            try:
                now = time.monotonic()
                base = _twin_graph(d - 2, now + 0.4 * (deadline - now), rng)
                consider(*base)
            except Exception:
                base = None
        # Generalized quadrangle W(d-1) as an alternative base.
        if base is None and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
            try:
                base = _gq_incidence(d - 1)
                consider(*base)
            except Exception:
                base = None

        if base is not None and time.monotonic() < deadline - 0.5:
            try:
                n3, e3 = _ils(base[0], base[1], d, deadline, rng)
                consider(n3, e3)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
