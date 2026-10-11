"""Bipartite degree-diameter search with a new move set: degree-preserving
edge switches, plus "absorb" moves that pull edges toward freshly added
vertices. Each attempt adds one A-vertex and one B-vertex to the best valid
graph, then runs Metropolis annealing on the count of bad pairs (distance > D).
Adding edges never increases distances, so deficient capacity is always
saturated greedily.
"""
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Known bases (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph when q = d - 2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


# ----------------------------------------------------------------------------
# Helpers.
# ----------------------------------------------------------------------------

def _bipartition(n, edges):
    """Proper 2-colouring (0/1) of a bipartite graph on 0..n-1."""
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
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


class _Ext:
    """Mutable bipartite graph with degree cap d, scored by bad pairs at radius D.

    Moves (all keep the graph bipartite and degrees <= d):
      switch : (a,b),(c,e) -> (a,e),(c,b)            degree-preserving
      absorb : (a,b) -> (x,b),(a,y), x,y deficient   fills deficient capacity
      add    : add (x,y) between deficient vertices  (never hurts distances)
    """

    def __init__(self, n, color, edges, d, D, rng):
        self.n = n
        self.color = color
        self.d = d
        self.D = D
        self.rng = rng
        self.adj = [set() for _ in range(n)]
        for u, v in edges:
            self.adj[u].add(v)
            self.adj[v].add(u)
        self.A = [v for v in range(n) if color[v] == 0]
        self.B = [v for v in range(n) if color[v] == 1]

    def _add(self, a, b, log):
        self.adj[a].add(b)
        self.adj[b].add(a)
        log.append((a, b, 1))

    def _rem(self, a, b, log):
        self.adj[a].discard(b)
        self.adj[b].discard(a)
        log.append((a, b, 0))

    def _undo(self, log):
        for a, b, t in reversed(log):
            if t:
                self.adj[a].discard(b)
                self.adj[b].discard(a)
            else:
                self.adj[a].add(b)
                self.adj[b].add(a)

    def cost(self):
        """Number of unordered pairs at distance > D (unreachable pairs included)."""
        n, adj = self.n, self.adj
        reach = [1 << v for v in range(n)]
        for _ in range(self.D):
            new = [0] * n
            for v in range(n):
                r = reach[v]
                for u in adj[v]:
                    r |= reach[u]
                new[v] = r
            reach = new
        return sum(n - r.bit_count() for r in reach) // 2

    def saturate(self):
        """Greedily add edges between deficient opposite-side vertices (never hurts)."""
        d, adj, rng = self.d, self.adj, self.rng
        log = []
        xs = [x for x in self.A if len(adj[x]) < d]
        ys = [y for y in self.B if len(adj[y]) < d]
        rng.shuffle(xs)
        for x in xs:
            if len(adj[x]) >= d:
                continue
            cand = [y for y in ys if len(adj[y]) < d and y not in adj[x]]
            rng.shuffle(cand)
            for y in cand:
                if len(adj[x]) >= d:
                    break
                if len(adj[y]) < d:
                    self._add(x, y, log)

    def move(self):
        """Propose one move; return its undo log, or None if it was not applicable."""
        rng, adj, d = self.rng, self.adj, self.d
        A, B = self.A, self.B
        log = []
        r = rng.random()
        if r < 0.45:  # degree-preserving switch
            a = rng.choice(A)
            c = rng.choice(A)
            if a == c or not adj[a] or not adj[c]:
                return None
            b = rng.choice(tuple(adj[a]))
            e = rng.choice(tuple(adj[c]))
            if b == e or e in adj[a] or b in adj[c]:
                return None
            self._rem(a, b, log)
            self._rem(c, e, log)
            self._add(a, e, log)
            self._add(c, b, log)
        elif r < 0.9:  # absorb: pull an edge toward deficient x (A) and y (B)
            xs = [x for x in A if len(adj[x]) < d]
            ys = [y for y in B if len(adj[y]) < d]
            if not xs or not ys:
                return None
            x = rng.choice(xs)
            y = rng.choice(ys)
            a = rng.choice(A)
            if not adj[a]:
                return None
            b = rng.choice(tuple(adj[a]))
            if x == a or y == b or b in adj[x] or y in adj[a]:
                return None
            self._rem(a, b, log)
            self._add(x, b, log)
            self._add(a, y, log)
        else:  # add an edge between two deficient vertices
            xs = [x for x in A if len(adj[x]) < d]
            ys = [y for y in B if len(adj[y]) < d]
            if not xs or not ys:
                return None
            x = rng.choice(xs)
            y = rng.choice(ys)
            if y in adj[x]:
                return None
            self._add(x, y, log)
        return log

    def run(self, deadline, T0=2.0, T1=0.2):
        """Anneal until cost 0 or the deadline. Returns True on success."""
        self.saturate()
        cur = self.cost()
        if cur == 0:
            return True
        t0 = time.monotonic()
        span = max(1e-6, deadline - t0)
        while cur > 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
            log = self.move()
            if log is None:
                continue
            c2 = self.cost()
            delta = c2 - cur
            if delta <= 0 or self.rng.random() < math.exp(-delta / T):
                cur = c2
            else:
                self._undo(log)
        return cur == 0

    def edges(self):
        out = []
        for u in range(self.n):
            if self.color[u] == 0:
                for v in self.adj[u]:
                    out.append((u, v))
        return out


def _try_extend(n, edges, d, D, deadline, rng):
    """Add one A-vertex and one B-vertex to a valid graph and anneal to diameter D."""
    color = _bipartition(n, edges) + [0, 1]
    ext = _Ext(n + 2, color, edges, d, D, rng)
    if ext.run(deadline):
        return ext.n, ext.edges()
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    # Known bases for diameter 3 (and valid for larger D as well).
    for make in (lambda: _araujo(d), lambda: _best_pg(d)):
        try:
            cand = make()
        except (ValueError, AssertionError):
            cand = None
        if cand is not None and cand[0] > best_n and lib.is_valid(cand[0], cand[1], d, D):
            best_n, best_e = cand

    # Skip extension when the base already meets the Moore bound.
    if best_n >= lib._moore_bound(d, D):
        return best_n, best_e

    # Repeated attempts: add a vertex pair to the current best and anneal.
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        budget = remaining * 0.6 if remaining > 3 else remaining
        attempt_deadline = time.monotonic() + budget
        res = _try_extend(best_n, best_e, d, D, attempt_deadline, rng)
        if res is not None:
            n2, e2 = res
            if lib.is_valid(n2, e2, d, D):
                best_n, best_e = n2, e2
        if best_n >= lib._moore_bound(d, D):
            break

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
