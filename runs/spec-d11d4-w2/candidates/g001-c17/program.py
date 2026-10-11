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
# NEW ENGINE: mutable graph with iterated local search for diameter 4.
#
# Invariant: the graph is always valid (bipartite, max degree d, diameter <= 4
# over alive vertices). Growth adds a vertex x on side X joined to a set S on
# the opposite side whose radius-3 balls cover every alive vertex; this keeps
# diameter <= 4. Perturbation removes random vertices, keeping only removals
# that preserve diameter <= 4. Removal frees degree, so later growth can
# choose different covers. The best state seen is kept and restored when the
# search drifts too far below it.
# ----------------------------------------------------------------------------

def _two_color(n, adj):
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


def _reach(adj, N, k):
    """Per-slot bitmask of all slots within distance k."""
    reach = [1 << v for v in range(N)]
    for _ in range(k):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


class _Graph:
    def __init__(self, n, edges, d):
        self.d = d
        self.N = n
        self.adj = [set() for _ in range(n)]
        for u, v in edges:
            self.adj[u].add(v)
            self.adj[v].add(u)
        self.color = _two_color(n, self.adj)
        self.alive = [True] * n
        self.alive_mask = (1 << n) - 1
        self.free = []
        self.count = n

    def snap(self):
        return ([set(s) for s in self.adj], list(self.color), list(self.alive),
                self.alive_mask, self.N, list(self.free), self.count)

    def load(self, st):
        adj, color, alive, mask, N, free, count = st
        self.adj = [set(s) for s in adj]
        self.color = list(color)
        self.alive = list(alive)
        self.alive_mask = mask
        self.N = N
        self.free = list(free)
        self.count = count

    def add_vertex(self, S, col):
        if self.free:
            x = self.free.pop()
            self.adj[x] = set(S)
        else:
            x = self.N
            self.N += 1
            self.adj.append(set(S))
            self.color.append(col)
            self.alive.append(False)
        self.color[x] = col
        self.alive[x] = True
        self.alive_mask |= 1 << x
        for s in S:
            self.adj[s].add(x)
        self.count += 1

    def remove_vertex(self, x):
        nb = set(self.adj[x])
        for s in nb:
            self.adj[s].discard(x)
        self.adj[x] = set()
        self.alive[x] = False
        self.alive_mask &= ~(1 << x)
        self.free.append(x)
        self.count -= 1
        return nb

    def restore_vertex(self, x, nb):
        self.free.remove(x)
        self.adj[x] = set(nb)
        for s in nb:
            self.adj[s].add(x)
        self.alive[x] = True
        self.alive_mask |= 1 << x
        self.count += 1

    def export(self):
        ids = [v for v in range(self.N) if self.alive[v]]
        idx = {v: i for i, v in enumerate(ids)}
        edges = [(idx[v], idx[u]) for v in ids for u in self.adj[v] if v < u]
        return len(ids), edges


def _diam_ok(g):
    R = _reach(g.adj, g.N, 4)
    am = g.alive_mask
    return all((R[v] & am) == am for v in range(g.N) if g.alive[v])


def _cover(s0, pool_all, R3, am, d, rng, noise):
    """Greedy cover of alive vertices by R3 balls of s0 plus up to d-1 pool vertices; None if impossible."""
    S = [s0]
    unc = am & ~R3[s0]
    pool = list(pool_all)
    while unc and len(S) < d and pool:
        gains = [(R3[v] & unc).bit_count() for v in pool]
        best = max(gains)
        if best <= 0:
            break
        if noise > 0.0 and rng.random() < noise:
            thr = max(1, int(best * 0.8))
            choices = [i for i, gg in enumerate(gains) if gg >= thr]
        else:
            choices = [i for i, gg in enumerate(gains) if gg == best]
        i = rng.choice(choices)
        bv = pool[i]
        S.append(bv)
        unc &= ~R3[bv]
        pool[i] = pool[-1]
        pool.pop()
    return None if unc else S


def _grow(g, rng, deadline):
    """Add vertices greedily until no seed admits a valid cover (stall) or time runs out."""
    added = 0
    while time.monotonic() < deadline:
        R3 = _reach(g.adj, g.N, 3)
        am = g.alive_mask
        spare = [v for v in range(g.N) if g.alive[v] and len(g.adj[v]) < g.d]
        if not spare:
            break
        seeds = rng.sample(spare, min(len(spare), 12))
        done = False
        for s0 in seeds:
            pool_all = [v for v in spare if v != s0 and g.color[v] == g.color[s0]]
            for attempt in range(4):
                S = _cover(s0, pool_all, R3, am, g.d, rng, 0.0 if attempt == 0 else 0.35)
                if S is not None:
                    g.add_vertex(S, 1 - g.color[s0])
                    done = True
                    break
            if done:
                break
        if not done:
            break
        added += 1
    return added


def _perturb(g, rng, k):
    """Remove k random vertices, keeping each removal only if diameter <= 4 still holds."""
    for _ in range(k):
        alive = [v for v in range(g.N) if g.alive[v]]
        if len(alive) <= 2:
            return
        x = rng.choice(alive)
        nb = g.remove_vertex(x)
        if not _diam_ok(g):
            g.restore_vertex(x, nb)


def _ils(g, rng, deadline):
    """Iterated local search: grow, perturb, grow; keep the best valid state."""
    if not any(g.alive[v] and len(g.adj[v]) < g.d for v in range(g.N)):
        return
    _grow(g, rng, deadline)
    best_c = g.count
    best = g.snap()
    while time.monotonic() < deadline:
        _perturb(g, rng, rng.randint(1, 3))
        _grow(g, rng, deadline)
        if g.count > best_c:
            best_c = g.count
            best = g.snap()
        elif g.count < best_c - 2:
            g.load(best)
    g.load(best)


def _best_q(m):
    """Largest prime power q with 2 <= q <= min(m, 11), or None."""
    for q in range(min(m, 11), 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
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

    if D >= 4:
        # Generalized quadrangle W(d-1): degree d, diameter 4 (no spare degree).
        if lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
            try:
                consider(*_gq_incidence(d - 1))
            except Exception:
                pass

        # Phase A: twin graph on W(d-2), then iterated local search with the spare slots.
        if lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
            try:
                n2, e2 = _twin_graph(d - 2, t0 + 0.25 * budget, rng)
                if lib.is_valid(n2, e2, d, D):
                    consider(n2, e2)
                    g = _Graph(n2, e2, d)
                    _ils(g, rng, t0 + 0.5 * budget)
                    consider(*g.export())
            except Exception:
                pass

        # Phase B: plain W(q) incidence with q the largest prime power <= d-1,
        # leaving spare degree d-(q+1) per vertex for the local search.
        q = _best_q(d - 1)
        if q is not None and q + 1 < d:
            try:
                n1, e1 = _gq_incidence(q)
                g = _Graph(n1, e1, d)
                _ils(g, rng, deadline)
                consider(*g.export())
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
