import math
import random
import time

import lib


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost(n, adj, D):
    """Ordered pairs (u, v) with dist(u, v) > D (unreachable counts). Zero means diameter <= D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


class _Search:
    """Bipartite graph under degree-<=d edits, scored by the number of pairs farther than D apart.

    Vertices carry a fixed colour (0 or 1); every edge is stored as (a, b) with colour(a) = 0.
    Moves: degree-preserving double-edge swaps, and adding an edge between two deficient vertices.
    """

    def __init__(self, n, color, edges, d, D, rng):
        self.d = d
        self.D = D
        self.rng = rng
        self.n = n
        self.color = list(color)
        self.adj = [set() for _ in range(n)]
        self.E = []
        self.pos = {}
        self.cur = None
        for a, b in edges:
            self._add(*self._key(a, b))

    def _key(self, x, y):
        return (x, y) if self.color[x] == 0 else (y, x)

    def _add(self, a, b):
        self.pos[(a, b)] = len(self.E)
        self.E.append((a, b))
        self.adj[a].add(b)
        self.adj[b].add(a)

    def _remove(self, a, b):
        i = self.pos.pop((a, b))
        last = self.E.pop()
        if i < len(self.E):
            self.E[i] = last
            self.pos[last] = i
        self.adj[a].discard(b)
        self.adj[b].discard(a)

    def cost(self):
        self.cur = _cost(self.n, self.adj, self.D)
        return self.cur

    def state(self):
        return self.n, list(self.color), list(self.E)

    def insert(self, c):
        """Add a vertex of colour c, stealing edges from full vertices when needed."""
        v = self.n
        self.n += 1
        self.color.append(c)
        self.adj.append(set())
        opp = 1 - c
        rng = self.rng
        deficient = [u for u in range(v) if self.color[u] == opp and len(self.adj[u]) < self.d]
        full = [u for u in range(v) if self.color[u] == opp and len(self.adj[u]) >= self.d]
        rng.shuffle(deficient)
        rng.shuffle(full)
        chosen = deficient[:self.d]
        need = self.d - len(chosen)
        for a in full[:need]:
            b = rng.choice(list(self.adj[a]))
            self._remove(*self._key(a, b))
            chosen.append(a)
        for u in chosen:
            self._add(*self._key(u, v))

    def move(self, T):
        rng = self.rng
        if rng.random() < 0.15:
            d0 = [u for u in range(self.n) if self.color[u] == 0 and len(self.adj[u]) < self.d]
            d1 = [u for u in range(self.n) if self.color[u] == 1 and len(self.adj[u]) < self.d]
            if d0 and d1:
                a = rng.choice(d0)
                b = rng.choice(d1)
                if b not in self.adj[a]:
                    self._add(a, b)
                    self.cost()
            return
        if len(self.E) < 2:
            return
        a, b = rng.choice(self.E)
        c, e = rng.choice(self.E)
        if a == c or b == e:
            return
        if e in self.adj[a] or b in self.adj[c]:
            return
        old = self.cur
        self._remove(a, b)
        self._remove(c, e)
        self._add(a, e)
        self._add(c, b)
        new = self.cost()
        if new <= old or rng.random() < math.exp(-(new - old) / T):
            return
        self._remove(a, e)
        self._remove(c, b)
        self._add(a, b)
        self._add(c, e)
        self.cur = old


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.75 * time_limit - 1.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_e = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2, always a fallback

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if d == 2:
        n = 2 * D
        cyc = sorted({(min(i, (i + 1) % n), max(i, (i + 1) % n)) for i in range(n)})
        consider(n, cyc)
        return best_n, best_e

    mb = 2 * sum((d - 1) ** i for i in range(D))  # Moore bound for bipartite graphs
    if best_n >= mb:
        return best_n, best_e

    if D >= 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if best_n >= mb:
        return best_n, best_e

    rng = random.Random(seed * 1000003 + d * 131 + D)

    half = best_n // 2
    base_color = [0 if v < half else 1 for v in range(best_n)]
    S = _Search(best_n, base_color, best_e, d, D, rng)
    S.cost()
    good_n, good_color, good_E = S.state()
    stall = 0

    while time.monotonic() < deadline:
        if S.cur == 0:
            good_n, good_color, good_E = S.state()
            if S.n > best_n:
                consider(S.n, list(S.E))
            if best_n >= mb:
                break
            S.insert(rng.randrange(2))
            S.cost()
            stall = 0
        else:
            T = rng.choice((0.1, 0.3, 0.6, 1.0, 2.0))
            for _ in range(100):
                S.move(T)
                if S.cur == 0 or time.monotonic() >= deadline:
                    break
            stall += 100
            if stall >= 2000:
                S = _Search(good_n, good_color, good_E, d, D, rng)
                S.cost()
                stall = 0

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
