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
# Diameter-4 extension primitives: a new vertex x joined to a set S of spare
# vertices on the opposite side keeps diameter <= 4 exactly when the union of
# R3(s) over s in S covers every existing vertex.
# ----------------------------------------------------------------------------

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
    """Choose the next cover vertex: best gain, or a random useful one with probability noise."""
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


# ----------------------------------------------------------------------------
# NEW: ruin-and-recreate search over valid prefixes.
#
# Every graph obtained by appending extension vertices to a valid diameter-4
# graph is itself valid, and removing the most recently added vertices returns
# an earlier valid graph. So the search walks through valid snapshots:
#   1. grow greedily (randomized set cover) until it stalls,
#   2. record the best snapshot,
#   3. roll back a random number of the newest vertices (ruin),
#   4. grow again with fresh randomness (recreate).
# If the current state drifts well below the best, it restarts from the best.
# ----------------------------------------------------------------------------

class _Graph:
    """Bipartite graph with incremental append and LIFO rollback of added vertices."""
    __slots__ = ("n", "edges", "adj", "color")

    def __init__(self, n, edges):
        self.n = n
        self.edges = list(edges)
        self.adj = [[] for _ in range(n)]
        for u, v in self.edges:
            self.adj[u].append(v)
            self.adj[v].append(u)
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

    def attach(self, S, side):
        """Append a new vertex on the given side joined to S; return its label."""
        x = self.n
        for s in S:
            self.edges.append((s, x))
            self.adj[s].append(x)
        self.adj.append(list(S))
        self.color.append(side)
        self.n += 1
        return x

    def rollback(self, newn):
        """Remove every vertex with label >= newn (they are the most recently attached)."""
        while self.edges and max(self.edges[-1]) >= newn:
            u, v = self.edges.pop()
            s, x = (u, v) if u < v else (v, u)
            self.adj[s].remove(x)
        del self.adj[newn:]
        del self.color[newn:]
        self.n = newn


def _try_add(g, d, reach, full, rng, noise):
    """One randomized cover attempt. Returns True if a vertex was added, False on failure, None if no spare slots."""
    spare = [v for v in range(g.n) if len(g.adj[v]) < d]
    if not spare:
        return None
    s0 = rng.choice(spare)
    pool = [v for v in spare if g.color[v] == g.color[s0] and v != s0]
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
        return False
    g.attach(S, 1 - g.color[s0])
    return True


def _grow(g, d, deadline, rng, noise, max_fails):
    """Add vertices until max_fails consecutive cover attempts fail or no spare slots remain."""
    fails = 0
    reach = None
    full = 0
    while fails < max_fails and time.monotonic() < deadline:
        if reach is None:
            reach = _ball3(g.n, g.adj)
            full = (1 << g.n) - 1
        r = _try_add(g, d, reach, full, rng, noise)
        if r is None:
            return
        if r:
            reach = None
            fails = 0
        else:
            fails += 1


def _ruin_and_recreate(base_n, base_edges, d, deadline, rng):
    """Search over valid prefixes of the base graph; return the best (n, edges) found."""
    g = _Graph(base_n, base_edges)
    best_n = base_n
    best_edges = list(base_edges)
    while time.monotonic() < deadline:
        noise = rng.choice([0.1, 0.25, 0.4])
        _grow(g, d, deadline, rng, noise, max_fails=150)
        if g.n > best_n:
            best_n = g.n
            best_edges = list(g.edges)
        elif g.n < best_n - 3:
            g = _Graph(best_n, best_edges)
        added = g.n - base_n
        if added > 0:
            k = rng.randint(1, min(added, 8))
            g.rollback(g.n - k)
    return best_n, best_edges


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
    if D == 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # Generalized quadrangle W(d-1): degree d, diameter 4 (no spare slots, fallback only).
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Twin graph on W(d-2) with degree d, then ruin-and-recreate extension.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        q = d - 2
        base = None
        try:
            now = time.monotonic()
            base = _twin_graph(q, now + 0.3 * (deadline - now), rng)
            consider(*base)
        except Exception:
            base = None

        if base is not None and lib.is_valid(base[0], base[1], d, D):
            try:
                n2, e2 = _ruin_and_recreate(base[0], base[1], d, deadline, rng)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
