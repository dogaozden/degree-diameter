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
# Ruin-and-recreate on a diameter-4 bipartite graph with spare degree.
#
# New helper in this version: a mutable state (_St) supports removing an added
# vertex. Ruin step: delete a random added vertex x (only if the diameter-4
# property survives), regrow with the randomized set-cover extension, and keep
# the result if the number of live vertices did not drop; otherwise roll back
# to a snapshot. This lets the search drift across plateaus and reclaim the
# degree freed by removed vertices.
#
# A new vertex x on side X joined to S (all on side Y, same colour) keeps
# diameter <= 4 exactly when the union of R3(s), s in S, covers every live
# vertex. Reach masks are recomputed after every successful addition, so the
# cover test is exact (not conservative).
# ----------------------------------------------------------------------------

NOISE = 0.25


class _St:
    """Mutable bipartite graph with live/dead flags, used by the ruin-and-recreate search."""

    def __init__(self, n, edges):
        self.n = n
        self.adj = [set() for _ in range(n)]
        for u, v in edges:
            self.adj[u].add(v)
            self.adj[v].add(u)
        self.alive = [True] * n
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

    def snap(self):
        return (self.n, [set(a) for a in self.adj], list(self.alive), list(self.color))

    def restore(self, s):
        self.n, adj, self.alive, self.color = s
        self.adj = adj

    def count(self):
        return sum(self.alive)


def _alive_mask(st):
    m = 0
    for v in range(st.n):
        if st.alive[v]:
            m |= 1 << v
    return m


def _reach(st, R):
    """Per-vertex bitmask of live vertices within distance R (dead vertices get 0)."""
    n, alive, adj = st.n, st.alive, st.adj
    reach = [(1 << v) if alive[v] else 0 for v in range(n)]
    for _ in range(R):
        new = [0] * n
        for v in range(n):
            if alive[v]:
                r = reach[v]
                for u in adj[v]:
                    r |= reach[u]
                new[v] = r
        reach = new
    return reach


def _diam_ok(st, R):
    full = _alive_mask(st)
    reach = _reach(st, R)
    return all(reach[v] == full for v in range(st.n) if st.alive[v])


def _attempt(st, d, rng, reach, full):
    """Try to find a cover set S (same colour, spare degree) for a new vertex; return S or None."""
    alive, adj, color, n = st.alive, st.adj, st.color, st.n
    spare = [v for v in range(n) if alive[v] and len(adj[v]) < d]
    if not spare:
        return None
    s0 = rng.choice(spare)
    pool = [v for v in spare if v != s0 and color[v] == color[s0]]
    S = [s0]
    unc = full & ~reach[s0]
    while unc and len(S) < d and pool:
        if rng.random() < NOISE:
            useful = [v for v in pool if reach[v] & unc]
            if not useful:
                break
            bv = rng.choice(useful)
        else:
            bv, best = -1, 0
            for v in pool:
                g = (reach[v] & unc).bit_count()
                if g > best:
                    best, bv = g, v
            if bv < 0:
                break
        S.append(bv)
        unc &= ~reach[bv]
        pool.remove(bv)
    return None if unc else S


def _add(st, S):
    x = st.n
    st.n += 1
    st.adj.append(set(S))
    st.alive.append(True)
    st.color.append(1 - st.color[S[0]])
    for s in S:
        st.adj[s].add(x)


def _grow(st, d, rng, deadline, max_fail):
    """Greedily add vertices with exact diameter-4 cover tests until max_fail consecutive failures."""
    fails = 0
    reach = None
    full = 0
    while time.monotonic() < deadline and fails < max_fail:
        if reach is None:
            reach = _reach(st, 3)
            full = _alive_mask(st)
        S = _attempt(st, d, rng, reach, full)
        if S is None:
            fails += 1
            continue
        _add(st, S)
        reach = None
        fails = 0


def _export(st):
    alive_ids = [v for v in range(st.n) if st.alive[v]]
    mp = {v: i for i, v in enumerate(alive_ids)}
    edges = []
    for v in alive_ids:
        for u in st.adj[v]:
            if v < u:
                edges.append((mp[v], mp[u]))
    return len(alive_ids), edges


def _ruin_recreate(st, n0, d, rng, deadline):
    """Repeatedly remove a random added vertex, regrow, and keep the result if the live count did not drop."""
    while time.monotonic() < deadline:
        added = [v for v in range(n0, st.n) if st.alive[v]]
        if not added:
            break
        before = st.count()
        snap = st.snap()
        x = rng.choice(added)
        for u in st.adj[x]:
            st.adj[u].discard(x)
        st.adj[x] = set()
        st.alive[x] = False
        if not _diam_ok(st, 4):
            st.restore(snap)
            continue
        _grow(st, d, rng, deadline, 30)
        if st.count() < before:
            st.restore(snap)


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

    # Twin graph on W(d-2), then exact ruin-and-recreate search using spare slots.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            st = _St(n2, e2)
            _grow(st, d, rng, deadline, 400)
            consider(*_export(st))
            _ruin_recreate(st, n2, d, rng, deadline)
            consider(*_export(st))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
