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
# Shared helpers: radius-r reach masks, cover choice, mutable graph state.
# ----------------------------------------------------------------------------

NOISE = 0.25


def _ball(adj, n, radius):
    """Return per-vertex bitmasks of all vertices (ids) within distance `radius`."""
    reach = [1 << v for v in range(n)]
    for _ in range(radius):
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


def _colors(n, adj):
    """2-colour a bipartite graph by BFS (vertices with no edges get colour 0)."""
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


class _State:
    """Mutable graph with recyclable vertex ids. Dead ids are isolated and excluded by the alive mask."""

    def __init__(self, n, edges):
        self.adj = [set() for _ in range(n)]
        for u, v in edges:
            self.adj[u].add(v)
            self.adj[v].add(u)
        self.color = _colors(n, self.adj)
        self.alive = [True] * n
        self.free = []

    def copy(self):
        s = _State.__new__(_State)
        s.adj = [set(a) for a in self.adj]
        s.color = list(self.color)
        s.alive = list(self.alive)
        s.free = list(self.free)
        return s

    def size(self):
        return sum(1 for a in self.alive if a)

    def alive_mask(self):
        m = 0
        for v, a in enumerate(self.alive):
            if a:
                m |= 1 << v
        return m

    def new_vertex(self, c):
        if self.free:
            x = self.free.pop()
            self.alive[x] = True
            self.color[x] = c
            self.adj[x] = set()
        else:
            x = len(self.adj)
            self.adj.append(set())
            self.color.append(c)
            self.alive.append(True)
        return x

    def remove(self, x):
        for s in self.adj[x]:
            self.adj[s].discard(x)
        self.adj[x] = set()
        self.alive[x] = False
        self.free.append(x)

    def snapshot(self):
        ids = [v for v in range(len(self.adj)) if self.alive[v]]
        idx = {v: i for i, v in enumerate(ids)}
        edges = [(idx[u], idx[v]) for u in ids for v in self.adj[u] if u < v]
        return len(ids), edges


def _refill(st, d, R, rng, deadline, max_fail):
    """Greedily add vertices joined to spare-degree vertices so every alive vertex is within R of the cover set.

    Adding a vertex never shortens existing distances, so diameter <= R+1 is preserved exactly
    when the cover condition holds.
    """
    fails = 0
    while fails < max_fail and time.monotonic() < deadline:
        n = len(st.adj)
        A = st.alive_mask()
        spare = [v for v in range(n) if st.alive[v] and len(st.adj[v]) < d]
        if not spare:
            break
        reach = _ball(st.adj, n, R)
        s0 = rng.choice(spare)
        pool = [v for v in spare if st.color[v] == st.color[s0] and v != s0]
        S = [s0]
        unc = A & ~reach[s0]
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
        x = st.new_vertex(1 - st.color[s0])
        for s in S:
            st.adj[s].add(x)
            st.adj[x].add(s)
        fails = 0


def _diam_ok(st, D):
    """True if every alive pair of vertices is within distance D."""
    n = len(st.adj)
    A = st.alive_mask()
    reach = _ball(st.adj, n, D)
    return all((reach[v] & A) == A for v in range(n) if st.alive[v])


# ----------------------------------------------------------------------------
# NEW: plateau local search ("remove-and-refill").
#
# Repeatedly delete a random vertex. If the remaining graph still has diameter
# <= D, refill the freed degree slots with the set-cover extension. Accept
# moves that do not shrink the graph, so the search can drift across plateaus
# and occasionally grow by one vertex.
# ----------------------------------------------------------------------------

def _local_search(st, d, D, rng, deadline, consider):
    R = D - 1
    cur = st
    cur_size = cur.size()
    best_size = cur_size
    while time.monotonic() < deadline:
        trial = cur.copy()
        ids = [v for v in range(len(trial.adj)) if trial.alive[v]]
        if not ids:
            break
        x = rng.choice(ids)
        trial.remove(x)
        if not _diam_ok(trial, D):
            continue
        _refill(trial, d, R, rng, deadline, 4)
        sz = trial.size()
        if sz >= cur_size:
            cur, cur_size = trial, sz
            if sz > best_size:
                best_size = sz
                n, e = cur.snapshot()
                consider(n, e)


# ----------------------------------------------------------------------------
# Cyclic Haar-graph search: generic fallback for cases with no structured
# construction. Random connection sets S of size d over Z_m, increasing m.
# ----------------------------------------------------------------------------

def _haar_search(d, deadline, D, rng, consider):
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            consider(*found)
            misses = 0
        else:
            misses += 1
        m += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    c_dl = t0 + 0.5 * budget          # end of constructive phase
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    structured = False

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            return True
        return False

    # Projective plane incidence graph: degree d, diameter 3 (Moore-optimal).
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            if consider(*lib.projective_plane_incidence(d - 1)):
                structured = True
        except Exception:
            pass
        if D == 3 and structured:
            return best

    # Twin graph on W(d-2), then set-cover extension using spare slots.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11 and time.monotonic() < c_dl:
        try:
            now = time.monotonic()
            n2, e2 = _twin_graph(d - 2, now + 0.5 * (c_dl - now), rng)
            if consider(n2, e2):
                structured = True
            st = _State(n2, e2)
            _refill(st, d, D - 1, rng, c_dl, 4000)
            if consider(*st.snapshot()):
                structured = True
        except Exception:
            pass

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11 and time.monotonic() < c_dl:
        try:
            if consider(*_gq_incidence(d - 1)):
                structured = True
        except Exception:
            pass

    # No structured construction succeeded: spend construction time on cyclic Haar lifts.
    if not structured and time.monotonic() < c_dl:
        _haar_search(d, c_dl, D, rng, consider)

    # Remaining time: plateau local search from the best graph found so far.
    if time.monotonic() < deadline:
        try:
            _local_search(_State(best[0], best[1]), d, D, rng, deadline, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
