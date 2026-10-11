import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases.
# ----------------------------------------------------------------------------

def _largest_pg_q(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
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

    edges = set()
    for j, L in enumerate(lines):
        for p in L:
            edges.add((p, P + j))
    return 2 * P, sorted(edges)


def _km_minus_matching(k):
    """K_{k,k} minus a perfect matching: degree k-1, bipartite, diameter 3 for k >= 3."""
    return 2 * k, [(a, k + b) for a in range(k) for b in range(k) if a != b]


def _base_specs(d, D):
    specs = []
    if D >= 4:
        for q in (9, 8, 7):
            if q + 1 <= d and lib.is_prime_power(q):
                specs.append(lambda q=q: _gq_w(q))
    if D >= 3:
        q = _largest_pg_q(d)
        if q is not None:
            specs.append(lambda q=q: lib.projective_plane_incidence(q))
    if D >= 3 and d >= 3:
        specs.append(lambda k=d - 1: _km_minus_matching(k))
    return specs


def _moore(d, D):
    try:
        return lib._moore_bound(d, D)
    except Exception:
        return 10 ** 18


# ----------------------------------------------------------------------------
# Mutable bipartite graph state with diameter-preserving growth.
# ----------------------------------------------------------------------------

def _color_of(n, adj):
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
    return color


class _G:
    def __init__(self, n, edges, d, D):
        self.d = d
        self.D = D
        self.n = n
        sets = [set() for _ in range(n)]
        for u, v in edges:
            if u != v:
                sets[u].add(v)
                sets[v].add(u)
        self.adj = [sorted(s) for s in sets]
        self.alive = [True] * n
        self.count = n
        self.added = []
        self.color = _color_of(n, self.adj)

    def copy(self):
        g = _G.__new__(_G)
        g.d = self.d
        g.D = self.D
        g.n = self.n
        g.adj = [list(a) for a in self.adj]
        g.alive = list(self.alive)
        g.count = self.count
        g.added = list(self.added)
        g.color = list(self.color)
        return g

    def _full(self):
        m = 0
        for v in range(self.n):
            if self.alive[v]:
                m |= 1 << v
        return m

    def _balls(self, r):
        ball = [(1 << v) if self.alive[v] else 0 for v in range(self.n)]
        for _ in range(r):
            nb = []
            for v in range(self.n):
                x = ball[v]
                for u in self.adj[v]:
                    x |= ball[u]
                nb.append(x)
            ball = nb
        return ball

    def valid(self):
        full = self._full()
        ball = self._balls(self.D)
        return all(ball[v] == full for v in range(self.n) if self.alive[v])

    def _cover(self, cands, ball, full, rng, noisy):
        pool = list(cands)
        covered = 0
        chosen = []
        while covered != full and len(chosen) < self.d and pool:
            gains = [(ball[s] & ~covered).bit_count() for s in pool]
            best = max(gains)
            if best <= 0:
                break
            if noisy and rng.random() < 0.3:
                opts = [i for i, g in enumerate(gains) if g > 0]
            else:
                opts = [i for i, g in enumerate(gains) if g == best]
            i = rng.choice(opts)
            s = pool.pop(i)
            chosen.append(s)
            covered |= ball[s]
        return chosen if covered == full else None

    def _add_vertex(self, color, nbrs):
        v = self.n
        self.n += 1
        self.adj.append([])
        self.color.append(color)
        self.alive.append(True)
        for s in nbrs:
            self.adj[v].append(s)
            self.adj[s].append(v)
        self.added.append(v)
        self.count += 1

    def grow(self, rng, deadline):
        """Add one vertex whose <= d neighbours cover everything within D-1."""
        if time.monotonic() >= deadline:
            return False
        full = self._full()
        ball = self._balls(self.D - 1)
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [s for s in range(self.n)
                     if self.alive[s] and self.color[s] == c and len(self.adj[s]) < self.d]
            if not cands:
                continue
            for attempt in range(4):
                chosen = self._cover(cands, ball, full, rng, attempt > 0)
                if chosen:
                    self._add_vertex(1 - c, chosen)
                    return True
        return False

    def grow_all(self, rng, deadline):
        while self.grow(rng, deadline):
            pass

    def saturate(self, rng):
        """Join deficient opposite-colour vertices. Adding edges never breaks the diameter."""
        L = [v for v in range(self.n)
             if self.alive[v] and self.color[v] == 0 and len(self.adj[v]) < self.d]
        R = [v for v in range(self.n)
             if self.alive[v] and self.color[v] == 1 and len(self.adj[v]) < self.d]
        rng.shuffle(L)
        rng.shuffle(R)
        for a in L:
            if len(self.adj[a]) >= self.d:
                continue
            nb = set(self.adj[a])
            for b in R:
                if len(self.adj[a]) >= self.d:
                    break
                if len(self.adj[b]) < self.d and b not in nb:
                    self.adj[a].append(b)
                    self.adj[b].append(a)
                    nb.add(b)

    def remove(self, v):
        for u in self.adj[v]:
            self.adj[u].remove(v)
        self.adj[v] = []
        self.alive[v] = False
        self.count -= 1

    def export(self):
        idx = [-1] * self.n
        k = 0
        for v in range(self.n):
            if self.alive[v]:
                idx[v] = k
                k += 1
        edges = []
        for v in range(self.n):
            if self.alive[v]:
                iv = idx[v]
                for u in self.adj[v]:
                    if u > v:
                        edges.append((iv, idx[u]))
        return k, edges


# ----------------------------------------------------------------------------
# Iterated local search: remove some added vertices, regrow, keep if not worse.
# ----------------------------------------------------------------------------

def _ils(st, deadline, rng, holder):
    cur = st
    holder[0] = cur.export()
    best_n = cur.count
    while time.monotonic() < deadline:
        trial = cur.copy()
        pool = [v for v in trial.added if trial.alive[v]]
        k = rng.choice((1, 1, 2, 2, 3))
        if pool:
            for v in rng.sample(pool, min(k, len(pool))):
                trial.remove(v)
        trial.grow_all(rng, deadline)
        trial.saturate(rng)
        if trial.count >= cur.count and trial.valid():
            cur = trial
            if cur.count > best_n:
                best_n = cur.count
                holder[0] = cur.export()


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _run(d, D, seed, time_limit, start, cands):
    rng = random.Random(seed)
    end = start + max(0.5, 0.8 * time_limit - 1.5)

    states = []
    for builder in _base_specs(d, D):
        if end - time.monotonic() < 3:
            break
        try:
            n0, e0 = builder()
        except Exception:
            continue
        st = _G(n0, e0, d, D)
        if not st.valid():
            continue
        st.grow_all(rng, end)
        st.saturate(rng)
        if st.valid():
            states.append(st)
            cands.append(st.export())

    states.sort(key=lambda s: -s.count)
    top = [s for s in states[:2] if s.count < _moore(d, D)]
    for i, st in enumerate(top):
        now = time.monotonic()
        sub_end = now + (end - now) / (len(top) - i)
        holder = [None]
        try:
            _ils(st, sub_end, rng, holder)
        except Exception:
            pass
        if holder[0] is not None:
            cands.append(holder[0])


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        fallback = (2, [(0, 1)])
    else:
        fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2

    cands = []
    try:
        _run(d, D, seed, time_limit, start, cands)
    except Exception:
        pass
    cands.append(fallback)
    cands.sort(key=lambda t: -t[0])
    for n, e in cands:
        try:
            if lib.is_valid(n, e, d, D):
                return n, e
        except Exception:
            continue
    return fallback
