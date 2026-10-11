import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4.
    Points are 0..P-1, lines are P..2P-1 (sides are the two halves)."""
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


def _base_graph(d, D):
    """Return (n, edges) of a diameter-appropriate base graph, or None."""
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                return lib.projective_plane_incidence(q)
        return None
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q):
                return _gq_w(q)
        return None
    return None


# ----------------------------------------------------------------------------
# Mutable bipartite state with edge index and adjacency sets.
# Edges are stored as (a, b) with color[a] == 0 and color[b] == 1.
# ----------------------------------------------------------------------------

class _State:
    def __init__(self, n, color, edges):
        self.n = n
        self.color = list(color)
        self.E = []
        self.pos = {}
        self.nb = [set() for _ in range(n)]
        for u, v in edges:
            if self.color[u] == 1:
                u, v = v, u
            self._add(u, v)

    def _add(self, a, b):
        self.pos[(a, b)] = len(self.E)
        self.E.append((a, b))
        self.nb[a].add(b)
        self.nb[b].add(a)

    def _rem(self, a, b):
        i = self.pos.pop((a, b))
        last = self.E.pop()
        if i < len(self.E):
            self.E[i] = last
            self.pos[last] = i
        self.nb[a].discard(b)
        self.nb[b].discard(a)

    def apply(self, rem, add):
        for a, b in rem:
            self._rem(a, b)
        for a, b in add:
            self._add(a, b)

    def undo(self, rem, add):
        for a, b in add:
            self._rem(a, b)
        for a, b in rem:
            self._add(a, b)

    def new_vertex(self, c):
        self.n += 1
        self.color.append(c)
        self.nb.append(set())
        return self.n - 1

    def snapshot(self):
        return (self.n, list(self.color), list(self.E))

    def bad(self, D):
        """Number of unordered pairs at distance > D (unreachable counts)."""
        n, nb = self.n, self.nb
        reach = [1 << v for v in range(n)]
        for _ in range(D):
            new = []
            for v in range(n):
                x = reach[v]
                for u in nb[v]:
                    x |= reach[u]
                new.append(x)
            reach = new
        return sum(n - r.bit_count() for r in reach) // 2


def _balls(n, nb, r):
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = reach[v]
            for u in nb[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return reach


# ----------------------------------------------------------------------------
# Cover-based attachment of a new vertex of colour c.
# ----------------------------------------------------------------------------

def _attach(st, v, c, d, D, rng):
    n = st.n
    nb = st.nb
    reach = _balls(n, nb, D - 1)
    cands = [s for s in range(n) if st.color[s] != c and s != v and len(nb[s]) < d]
    if not cands:
        return []
    full = (1 << n) - 1
    best_cov, best_sel = -1, []
    for attempt in range(4):
        covered = 1 << v
        chosen = []
        pool = set(cands)
        while len(chosen) < d and pool:
            gains = {s: (reach[s] & ~covered).bit_count() for s in pool}
            g = max(gains.values())
            if g == 0:
                break
            opts = [s for s in pool if gains[s] == g]
            s = min(opts) if attempt == 0 else rng.choice(opts)
            chosen.append(s)
            pool.discard(s)
            covered |= reach[s]
        cov = covered.bit_count()
        if cov > best_cov:
            best_cov, best_sel = cov, chosen
        if covered == full:
            break
    return best_sel


# ----------------------------------------------------------------------------
# Simulated annealing on bad-pair count with degree-preserving and
# degree-moving edge changes.
# ----------------------------------------------------------------------------

def _rand_add(st, left, right, d):
    spL = [x for x in left if len(st.nb[x]) < d]
    spR = [y for y in right if len(st.nb[y]) < d]
    if not spL or not spR:
        return [], []
    for _ in range(40):
        x = spL[0] if len(spL) == 1 else spL[_rng_pick(len(spL))]
        y = spR[0] if len(spR) == 1 else spR[_rng_pick(len(spR))]
        if y not in st.nb[x]:
            return [], [(x, y)]
    return [], []


_RNG = random.Random(0)


def _rng_pick(k):
    return _RNG.randrange(k)


def _two_switch(st, rng):
    m = len(st.E)
    if m < 2:
        return [], []
    for _ in range(30):
        i = rng.randrange(m)
        j = rng.randrange(m)
        a, b = st.E[i]
        c, e = st.E[j]
        if a == c or b == e or e in st.nb[a] or b in st.nb[c]:
            continue
        return [(a, b), (c, e)], [(a, e), (c, b)]
    return [], []


def _move(st, left, right, d, rng):
    m = len(st.E)
    if m == 0:
        return [], []
    a, b = st.E[rng.randrange(m)]
    xs = [x for x in left if len(st.nb[x]) < d or x == a]
    ys = [y for y in right if len(st.nb[y]) < d or y == b]
    if not xs or not ys:
        return [], []
    for _ in range(30):
        x = rng.choice(xs)
        y = rng.choice(ys)
        if x == a and y == b:
            continue
        if y in st.nb[x]:
            continue
        return [(a, b)], [(x, y)]
    return [], []


def _anneal(st, d, D, deadline, rng):
    cur = st.bad(D)
    T0 = 0.6
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    left = [v for v in range(st.n) if st.color[v] == 0]
    right = [v for v in range(st.n) if st.color[v] == 1]
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - start) / span
        T = T0 * (1.0 - frac) + 0.02
        r = rng.random()
        if r < 0.3:
            rem, add = _rand_add(st, left, right, d)
        elif r < 0.75:
            rem, add = _two_switch(st, rng)
        else:
            rem, add = _move(st, left, right, d, rng)
        if not rem and not add:
            continue
        st.apply(rem, add)
        new = st.bad(D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            st.undo(rem, add)
    return cur == 0


# ----------------------------------------------------------------------------
# Growth loop: add one left and one right vertex, repair with annealing,
# commit only when diameter is restored.
# ----------------------------------------------------------------------------

def _grow(st, d, D, deadline, rng, holder):
    while time.monotonic() < deadline:
        snap = st.snapshot()
        ok = False
        for attempt in range(2):
            v = st.new_vertex(0)
            for s in _attach(st, v, 0, d, D, rng):
                st._add(v, s)
            w = st.new_vertex(1)
            for s in _attach(st, w, 1, d, D, rng):
                st._add(s, w)
            budget = max(1.0, (deadline - time.monotonic()) / 8.0)
            slice_end = min(deadline, time.monotonic() + budget)
            if _anneal(st, d, D, slice_end, rng):
                ok = True
                break
            st = _State(*snap)
            if time.monotonic() >= deadline:
                break
        if not ok:
            break
        n = st.n
        edges = [(a, b) for a, b in st.E]
        if n > holder[0][0] and lib.is_valid(n, edges, d, D):
            holder[0] = (n, edges)
    return st


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 1.0)
    deadline = start + total
    rng = random.Random(seed)
    global _RNG
    _RNG = rng

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = (n0, e0)
    if best[0] >= lib._moore_bound(d, D):
        return best

    try:
        base = _base_graph(d, D)
        if base is not None and base[0] > best[0] and lib.is_valid(base[0], base[1], d, D):
            best = base
            if best[0] >= lib._moore_bound(d, D):
                return best
            n, edges = base
            color = [0 if v < n // 2 else 1 for v in range(n)]
            st = _State(n, color, edges)
            if st.bad(D) == 0:
                holder = [best]
                _grow(st, d, D, deadline, rng, holder)
                best = holder[0]
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
