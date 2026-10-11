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
# Set-cover vertex extension (shared by the greedy and the swap search).
#
# Let R_{D-1}(v) be the set of vertices within distance D-1 of v. A new vertex
# x on side X, joined to a set S of spare-degree vertices on the opposite side,
# keeps diameter <= D exactly when the union of R_{D-1}(s), s in S, covers every
# alive vertex. Adding x only shortens distances, so no other pair can break.
# ----------------------------------------------------------------------------

NOISE = 0.25


def _ball3(n, adj):
    """Return per-vertex bitmasks of all vertices within distance 3 (list-based adjacency)."""
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


def _ballsets(adj, k):
    """Return per-slot bitmasks of all slots within distance k, for set-based adjacency (dead slots have no edges)."""
    n = len(adj)
    reach = [1 << v for v in range(n)]
    for _ in range(k):
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


def _extend(n, edges, d, deadline, rng):
    """Greedily add vertices while keeping max degree d and diameter 4; return (n, edges)."""
    edges = list(edges)
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

    MAX_FAILS = 20000
    fails = 0
    while time.monotonic() < deadline:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            if fails >= MAX_FAILS:
                return n, edges
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
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
            x = n
            n += 1
            for s in S:
                edges.append((s, x))
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - color[s0])
            fails = 0
            grown = True
            break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# NEW: remove-and-regrow swap search for diameter 4.
#
# State is a mutable graph with "slots": a removed vertex frees its slot, and a
# later addition reuses a free slot. One move picks a random alive vertex x,
# deletes it, then greedily regrows up to two vertices with the cover rule.
# Because deletion can break distances between old vertices, every candidate
# that is accepted is re-verified with a full radius-D ball check. Equal-size
# moves are accepted with probability 1/2, so the walk drifts across plateaus.
# ----------------------------------------------------------------------------

class _State:
    def __init__(self, adj, color, alive, alive_mask, free, count):
        self.adj = adj
        self.color = color
        self.alive = alive
        self.alive_mask = alive_mask
        self.free = free
        self.count = count

    @staticmethod
    def from_edges(n, edges):
        adj = [set() for _ in range(n)]
        for u, v in edges:
            adj[u].add(v)
            adj[v].add(u)
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
        return _State(adj, color, [True] * n, (1 << n) - 1, [], n)

    def copy(self):
        return _State([set(s) for s in self.adj], list(self.color), list(self.alive),
                      self.alive_mask, list(self.free), self.count)

    def remove(self, x):
        for s in self.adj[x]:
            self.adj[s].discard(x)
        self.adj[x] = set()
        self.alive[x] = False
        self.alive_mask &= ~(1 << x)
        self.free.append(x)
        self.count -= 1

    def add(self, S, side):
        if self.free:
            x = self.free.pop()
            self.alive[x] = True
            self.color[x] = side
            self.adj[x] = set(S)
        else:
            x = len(self.adj)
            self.adj.append(set(S))
            self.color.append(side)
            self.alive.append(True)
        for s in S:
            self.adj[s].add(x)
        self.alive_mask |= 1 << x
        self.count += 1
        return x

    def valid(self, D):
        reach = _ballsets(self.adj, D)
        m = self.alive_mask
        return all(reach[v] & m == m for v in range(len(self.adj)) if self.alive[v])

    def to_graph(self):
        idx = {}
        for v in range(len(self.adj)):
            if self.alive[v]:
                idx[v] = len(idx)
        edges = [(idx[u], idx[v]) for u in range(len(self.adj)) if self.alive[u]
                 for v in self.adj[u] if u < v]
        return len(idx), edges


def _grow(st, d, rad, rng, max_add, tries, deadline):
    """Add up to max_add vertices covering all alive vertices within distance rad+1; return number added."""
    added = 0
    while added < max_add and time.monotonic() < deadline:
        reach = _ballsets(st.adj, rad)
        spare = [v for v in range(len(st.adj)) if st.alive[v] and len(st.adj[v]) < d]
        if not spare:
            break
        found = None
        for _ in range(tries):
            s0 = rng.choice(spare)
            pool = [v for v in spare if st.color[v] == st.color[s0] and v != s0]
            S = [s0]
            unc = st.alive_mask & ~reach[s0]
            while unc and len(S) < d and pool:
                bv = _pick(pool, reach, unc, rng)
                if bv < 0:
                    break
                S.append(bv)
                unc &= ~reach[bv]
                pool.remove(bv)
            if not unc:
                found = S
                break
        if found is None:
            break
        st.add(found, 1 - st.color[found[0]])
        added += 1
    return added


def _swap_search(n, edges, d, D, rng, deadline):
    """Remove-and-regrow local search from a valid graph; return the best (n, edges) found."""
    cur = _State.from_edges(n, edges)
    best = cur
    while time.monotonic() < deadline:
        alive = [v for v in range(len(cur.adj)) if cur.alive[v]]
        if not alive:
            break
        x = rng.choice(alive)
        work = cur.copy()
        work.remove(x)
        _grow(work, d, D - 1, rng, 2, 30, deadline)
        if work.count > cur.count:
            ok = work.valid(D)
        elif work.count == cur.count and rng.random() < 0.5:
            ok = work.valid(D)
        else:
            ok = False
        if ok:
            cur = work
            if cur.count > best.count:
                best = cur
    return best.to_graph()


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

    # Twin graph on W(d-2), set-cover extension, then swap search for D = 4.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, t0 + 0.5 * budget, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, t0 + 0.7 * budget, rng)
            consider(n3, e3)
            if D == 4:
                consider(*_swap_search(n3, e3, d, D, rng, deadline))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
