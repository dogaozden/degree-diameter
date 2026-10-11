"""Grow-and-repair search for bipartite graphs with max degree d and diameter <= D.

Strategy:
1. Build the best algebraic base (Araujo-Pardo/Lopez record, else PG(2,q) incidence,
   else K_{d,d}) and grow it by cover extension, as before. This is the safe result.
2. New family: insert one vertex at a time into the current valid graph (stealing
   edges from full vertices when needed), then repair it with simulated annealing.
   Moves are degree-preserving edge switches plus greedy edge additions between
   deficient opposite-side vertices. The cost is the number of vertex pairs farther
   than D apart. Each stage that reaches cost 0 is kept as a new valid snapshot.
Every result is checked with lib.is_valid before it is accepted, and the K_{d,d}
fallback is returned if anything fails.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic bases.
# ----------------------------------------------------------------------------

def _araujo(d):
    """Araujo-Pardo & Lopez record graph (degree q+2) when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bipartition and cover-based growth (baseline extension).
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists; None if not bipartite."""
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
                elif color[v] == color[u]:
                    return None
    return color


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    if color is None:
        return n, edges

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(60):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    if color is None:
        return edges
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# New family: vertex insertion followed by annealed repair.
# ----------------------------------------------------------------------------

class _Graph:
    """Mutable bipartite graph; edges are stored as (A, B) with color[A] = 0."""

    def __init__(self, n, edges, color, d):
        self.n = n
        self.d = d
        self.color = list(color)
        self.adj = [set() for _ in range(n)]
        self.E = []
        self.pos = {}
        for u, v in edges:
            self._add(u, v)

    def _key(self, u, v):
        return (u, v) if self.color[u] == 0 else (v, u)

    def _add(self, u, v):
        k = self._key(u, v)
        self.pos[k] = len(self.E)
        self.E.append(k)
        self.adj[u].add(v)
        self.adj[v].add(u)

    def _rem(self, u, v):
        k = self._key(u, v)
        i = self.pos.pop(k)
        last = self.E.pop()
        if i < len(self.E):
            self.E[i] = last
            self.pos[last] = i
        self.adj[u].discard(v)
        self.adj[v].discard(u)

    def add_vertex(self, c, rng):
        """Insert a new vertex on side c, stealing an edge from a full vertex when short."""
        v = self.n
        self.n += 1
        self.color.append(c)
        self.adj.append(set())
        opp = 1 - c
        cands = [u for u in range(v) if self.color[u] == opp and len(self.adj[u]) < self.d]
        rng.shuffle(cands)
        for u in cands[:self.d]:
            self._add(u, v)
        short = self.d - len(cands[:self.d])
        if short > 0:
            full = [u for u in range(v) if self.color[u] == opp and len(self.adj[u]) == self.d]
            rng.shuffle(full)
            for b in full[:short]:
                a = rng.choice(list(self.adj[b]))
                self._rem(a, b)
                self._add(v, b)

    def saturate(self, rng):
        A = [u for u in range(self.n) if self.color[u] == 0 and len(self.adj[u]) < self.d]
        B = [u for u in range(self.n) if self.color[u] == 1 and len(self.adj[u]) < self.d]
        rng.shuffle(A)
        rng.shuffle(B)
        for a in A:
            for b in B:
                if len(self.adj[a]) >= self.d:
                    break
                if len(self.adj[b]) < self.d and b not in self.adj[a]:
                    self._add(a, b)

    def cost(self, D):
        """Number of unordered vertex pairs at distance more than D."""
        ball = [1 << v for v in range(self.n)]
        for _ in range(D):
            new = []
            for v in range(self.n):
                x = ball[v]
                for u in self.adj[v]:
                    x |= ball[u]
                new.append(x)
            ball = new
        return sum(self.n - b.bit_count() for b in ball) // 2


def _repair(g, D, rng, deadline, iters, T):
    """Simulated annealing on bad-pair cost using degree-preserving switches and edge additions."""
    cur = g.cost(D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        if rng.random() < 0.2:
            A = [u for u in range(g.n) if g.color[u] == 0 and len(g.adj[u]) < g.d]
            B = [u for u in range(g.n) if g.color[u] == 1 and len(g.adj[u]) < g.d]
            if A and B:
                a = rng.choice(A)
                b = rng.choice(B)
                if b not in g.adj[a]:
                    g._add(a, b)
                    cur = g.cost(D)
            continue
        m = len(g.E)
        if m < 2:
            continue
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = g.E[i]
        a2, b2 = g.E[j]
        if a == a2 or b == b2:
            continue
        if b2 in g.adj[a] or b in g.adj[a2]:
            continue
        g._rem(a, b)
        g._rem(a2, b2)
        g._add(a, b2)
        g._add(a2, b)
        c2 = g.cost(D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
        else:
            g._rem(a, b2)
            g._rem(a2, b)
            g._add(a, b)
            g._add(a2, b2)
    return cur == 0


def _grow_repair(n, edges, color, d, D, deadline, rng):
    """Repeatedly insert a vertex and repair; return the largest valid (n, edges) reached."""
    snap_n, snap_E, snap_color = n, list(edges), list(color)
    best = (n, list(edges))
    fails = 0
    while time.monotonic() < deadline and fails < 4:
        g = _Graph(snap_n, snap_E, snap_color, d)
        g.add_vertex(rng.randrange(2), rng)
        g.saturate(rng)
        if _repair(g, D, rng, deadline, 1500, 0.7):
            snap_n, snap_E, snap_color = g.n, list(g.E), list(g.color)
            best = (g.n, list(g.E))
            fails = 0
        else:
            fails += 1
    return best


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
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        rec = _araujo(d)
        if rec is not None:
            consider(rec[0], rec[1])
            n2, e2 = _grow(rec[0], rec[1], d, D, start + 0.2 * time_limit, rng)
            consider(n2, e2)

        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.25 * time_limit, rng)
            consider(n2, e2)

    # New family: grow-and-repair from the best valid graph found so far.
    if best_n <= 700:
        base_n, base_e = best
        color = _bipartition(base_n, lib.adjacency(base_n, base_e))
        if color is not None:
            n3, e3 = _grow_repair(base_n, base_e, color, d, D, deadline, rng)
            consider(n3, e3)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
