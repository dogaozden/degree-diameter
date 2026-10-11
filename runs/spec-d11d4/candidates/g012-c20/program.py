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
# Shared helpers.
# ----------------------------------------------------------------------------

def _two_color(n, adj):
    """Proper 2-colouring of a bipartite graph (every component starts at colour 0)."""
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


def _balls(n, adj, r):
    """Per-vertex bitmask of all vertices within distance r (dead vertices reach only themselves)."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return reach


# ----------------------------------------------------------------------------
# NEW ROUTINE 1: swap-improved k-cover.
#
# A new vertex x joined to S (|S| <= d, all on one side) keeps diameter D iff
# the balls of radius D-1 around S cover every alive vertex. The parent grows a
# cover greedily. Here the greedy cover is followed by a swap local search: for
# each member s of S, find the candidate that most shrinks the uncovered set
# given the other members, and swap it in when strictly better. This finds
# covers that pure greedy misses.
# ----------------------------------------------------------------------------

def _cover(reach, full, pool, d, rng, swap_rounds=2):
    """Return (S, uncovered_count) with S a subset of pool, |S| <= d, aiming to cover full."""
    S = []
    unc = full
    cand = list(pool)
    while unc and len(S) < d and cand:
        scored = []
        for v in cand:
            gain = (reach[v] & unc).bit_count()
            if gain:
                scored.append((gain, v))
        if not scored:
            break
        scored.sort(reverse=True)
        _, v = scored[rng.randrange(min(3, len(scored)))]
        S.append(v)
        cand.remove(v)
        unc &= ~reach[v]
    for _ in range(swap_rounds):
        if not unc:
            break
        moved = False
        inS = set(S)
        for i in range(len(S)):
            base = full
            for j, w in enumerate(S):
                if j != i:
                    base &= ~reach[w]
            cur = (base & ~reach[S[i]]).bit_count()
            bestv, bestc = None, cur
            for v in pool:
                if v in inS:
                    continue
                c = (base & ~reach[v]).bit_count()
                if c < bestc:
                    bestc, bestv = c, v
            if bestv is not None:
                inS.discard(S[i])
                S[i] = bestv
                inS.add(bestv)
                moved = True
        unc = full
        for w in S:
            unc &= ~reach[w]
        if not moved:
            break
    return S, unc.bit_count()


# ----------------------------------------------------------------------------
# Mutable bipartite graph with removable extension vertices.
# ----------------------------------------------------------------------------

class _G:
    def __init__(self, n, edges):
        self.n = n
        self.adj = [[] for _ in range(n)]
        for u, v in edges:
            self.adj[u].append(v)
            self.adj[v].append(u)
        self.color = _two_color(n, self.adj)
        self.alive = [True] * n
        self.added = []
        self.count = n

    def add_vertex(self, S, col):
        x = self.n
        self.n += 1
        self.adj.append(list(S))
        for s in S:
            self.adj[s].append(x)
        self.color.append(col)
        self.alive.append(True)
        self.added.append(x)
        self.count += 1
        return x

    def remove_vertex(self, x):
        for w in self.adj[x]:
            self.adj[w].remove(x)
        self.adj[x] = []
        self.alive[x] = False
        self.added.remove(x)
        self.count -= 1

    def snapshot(self):
        return ([list(a) for a in self.adj], list(self.color), list(self.alive),
                list(self.added), self.n, self.count)

    def restore(self, snap):
        adj, color, alive, added, n, count = snap
        self.adj = [list(a) for a in adj]
        self.color = list(color)
        self.alive = list(alive)
        self.added = list(added)
        self.n = n
        self.count = count

    def alive_mask(self):
        m = 0
        for v in range(self.n):
            if self.alive[v]:
                m |= 1 << v
        return m

    def edges(self):
        """Compacted (n, edges) over alive vertices."""
        idx = {}
        for v in range(self.n):
            if self.alive[v]:
                idx[v] = len(idx)
        E = []
        for v in range(self.n):
            if self.alive[v]:
                for w in self.adj[v]:
                    if v < w:
                        E.append((idx[v], idx[w]))
        return len(idx), E


def _grow(g, d, D, rng, deadline, max_fail):
    """Greedily append vertices whose cover (radius D-1) is complete, until max_fail consecutive misses."""
    R = D - 1
    reach = None
    full = 0
    fails = 0
    while fails < max_fail and time.monotonic() < deadline:
        if reach is None:
            reach = _balls(g.n, g.adj, R)
            full = g.alive_mask()
        spare = [v for v in range(g.n) if g.alive[v] and len(g.adj[v]) < d]
        if not spare:
            return
        ok = False
        for _ in range(2):
            s0 = rng.choice(spare)
            col = g.color[s0]
            pool = [v for v in spare if g.color[v] == col]
            S, cnt = _cover(reach, full, pool, d, rng)
            if cnt == 0 and S:
                g.add_vertex(S, 1 - col)
                ok = True
                break
        if ok:
            reach = None
            fails = 0
        else:
            fails += 1


def _diam_ok(g, D):
    reach = _balls(g.n, g.adj, D)
    full = g.alive_mask()
    return all((reach[v] & full) == full for v in range(g.n) if g.alive[v])


# ----------------------------------------------------------------------------
# NEW ROUTINE 2: iterated kick-and-regrow.
#
# Remove one random extension vertex (its neighbours regain spare degree),
# keep the result only if the diameter survives, regrow greedily with the
# swap-improved cover, and accept if the vertex count did not drop. Plateau
# moves are accepted to diversify. The best state seen is returned.
# ----------------------------------------------------------------------------

def _ils(g, d, D, rng, deadline):
    best_cnt = g.count
    best = g.edges()
    while time.monotonic() < deadline and g.added:
        snap = g.snapshot()
        before = g.count
        x = rng.choice(g.added)
        g.remove_vertex(x)
        if not _diam_ok(g, D):
            g.restore(snap)
            continue
        _grow(g, d, D, rng, deadline, 4)
        if g.count < before:
            g.restore(snap)
        elif g.count > best_cnt:
            best_cnt = g.count
            best = g.edges()
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

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

    # Twin graph on W(d-2), then cover-based growth and kick-and-regrow search.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, t0 + 0.4 * budget, rng)
            consider(n2, e2)
            g = _G(n2, e2)
            _grow(g, d, D, rng, t0 + 0.6 * budget, 400)
            consider(*g.edges())
            res = _ils(g, d, D, rng, t0 + budget)
            consider(*res)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
