import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Seed graphs: projective plane PG(2, q) (diameter 3) and generalized
# quadrangle W(q) incidence graph (diameter 4).
# ----------------------------------------------------------------------------

def _pg_seed(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _gq_seed(d):
    """W(q) for the largest prime power q <= min(d - 1, 5)."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bipartite edge-switch annealing with growth by edge insertion.
#
# State: a bipartite graph with sides given by `side`. Every edge is stored as
# (side0 vertex, side1 vertex). Moves are degree-preserving double edge swaps.
# Cost = number of unordered vertex pairs at distance > D.
# Growth adds one vertex per side: each of d steps moves an existing edge
# (x, y) to (a, y) and (x, b), so the new vertices a, b reach degree d while
# every old vertex keeps its degree.
# ----------------------------------------------------------------------------

def _bad_pairs(n, adj, D):
    """Unordered pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


class _State:
    def __init__(self, n, side, d):
        self.n = n
        self.d = d
        self.side = list(side)
        self.adj = [set() for _ in range(n)]
        self.elist = []
        self.eset = set()

    def add_edge(self, a, b):
        self.elist.append((a, b))
        self.eset.add((a, b))
        self.adj[a].add(b)
        self.adj[b].add(a)

    def replace(self, i, new):
        old = self.elist[i]
        self.eset.discard(old)
        self.adj[old[0]].discard(old[1])
        self.adj[old[1]].discard(old[0])
        self.elist[i] = new
        self.eset.add(new)
        self.adj[new[0]].add(new[1])
        self.adj[new[1]].add(new[0])

    def cost(self, D):
        return _bad_pairs(self.n, self.adj, D)

    def saturate(self, rng):
        """Join deficient opposite-side vertices greedily in random order."""
        d = self.d
        left = [v for v in range(self.n) if self.side[v] == 0 and len(self.adj[v]) < d]
        right = [v for v in range(self.n) if self.side[v] == 1 and len(self.adj[v]) < d]
        pairs = [(a, b) for a in left for b in right if b not in self.adj[a]]
        rng.shuffle(pairs)
        for a, b in pairs:
            if len(self.adj[a]) < d and len(self.adj[b]) < d and b not in self.adj[a]:
                self.add_edge(a, b)

    def grow(self, rng):
        """Insert one new vertex per side, each of degree d, by edge moves."""
        d = self.d
        a = self.n
        b = self.n + 1
        self.side.extend([0, 1])
        self.adj.extend([set(), set()])
        self.n += 2
        for _ in range(d):
            if not self.elist:
                break
            for _t in range(300):
                i = rng.randrange(len(self.elist))
                x, y = self.elist[i]
                if y in self.adj[a] or x in self.adj[b]:
                    continue
                self.replace(i, (a, y))
                self.add_edge(x, b)
                break
        self.saturate(rng)

    def edges(self):
        return list(self.elist)


def _state_from_edges(n, E, d):
    adj = [[] for _ in range(n)]
    for u, v in E:
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
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    st = _State(n, [max(c, 0) for c in color], d)
    for u, v in E:
        if u == v or (u, v) in st.eset or (v, u) in st.eset:
            continue
        a, b = (u, v) if st.side[u] == 0 else (v, u)
        if st.side[a] == st.side[b]:
            continue
        if (a, b) in st.eset:
            continue
        st.add_edge(a, b)
    return st


def _anneal(st, D, rng, deadline, stall_limit, T):
    """Degree-preserving edge-switch annealing. Returns the final cost (0 means success)."""
    cur = st.cost(D)
    best = cur
    since = 0
    while cur > 0:
        if time.monotonic() > deadline:
            break
        since += 1
        if since > stall_limit:
            break
        E = len(st.elist)
        if E < 2:
            break
        i = rng.randrange(E)
        j = rng.randrange(E)
        if i == j:
            continue
        a1, b1 = st.elist[i]
        a2, b2 = st.elist[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in st.eset or (a2, b1) in st.eset:
            continue
        st.replace(i, (a1, b2))
        st.replace(j, (a2, b1))
        c2 = st.cost(D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
            if cur < best:
                best = cur
                since = 0
        else:
            st.replace(j, (a2, b2))
            st.replace(i, (a1, b1))
    return cur


def _run_growth(n0, E0, d, D, deadline, rng, best_n):
    """Anneal-and-grow from a seed graph. Returns the best valid (n, edges) found, or None."""
    st = _state_from_edges(n0, E0, d)
    st.saturate(rng)
    found = None
    fails = 0
    while time.monotonic() < deadline:
        T = rng.uniform(0.4, 1.2)
        cur = _anneal(st, D, rng, deadline, stall_limit=6000, T=T)
        if cur > 0:
            fails += 1
            if fails >= 3:
                break
            continue
        fails = 0
        E = st.edges()
        if st.n > best_n and lib.is_valid(st.n, E, d, D):
            found = (st.n, E)
            best_n = st.n
        st.grow(rng)
    return found


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed * 1000003 + d * 31 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    seeds = []
    if D >= 4:
        gq = _gq_seed(d)
        if gq is not None and lib.is_valid(gq[0], gq[1], d, D):
            seeds.append(gq)
    if D >= 3:
        pg = _pg_seed(d)
        if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
            seeds.append(pg)

    for idx, (n0, E0) in enumerate(seeds):
        now = time.monotonic()
        if now >= deadline:
            break
        seed_deadline = now + (deadline - now) / (len(seeds) - idx)
        res = _run_growth(n0, E0, d, D, seed_deadline, rng, best_n)
        if res is not None and res[0] > best_n:
            best = res
            best_n = res[0]

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
        if not lib.is_valid(best[0], best[1], d, D):
            return 2, [(0, 1)]
    return best
