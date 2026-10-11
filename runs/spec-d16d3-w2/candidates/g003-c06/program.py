import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance more than D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


class _Graph:
    """Bipartite graph with fixed side colouring, edge list E of [A-end, B-end] pairs."""

    def __init__(self, n, color, edges, d):
        self.d = d
        self.color = list(color)
        self.adj = [[] for _ in range(n)]
        self.E = []
        for u, v in edges:
            a, b = (u, v) if self.color[u] == 0 else (v, u)
            self.E.append([a, b])
            self.adj[a].append(b)
            self.adj[b].append(a)

    @property
    def n(self):
        return len(self.adj)

    def replace(self, i, x, y):
        """Replace edge number i by (x, y), updating adjacency."""
        a, b = self.E[i]
        self.adj[a].remove(b)
        self.adj[b].remove(a)
        self.adj[x].append(y)
        self.adj[y].append(x)
        self.E[i] = [x, y]

    def snapshot(self):
        return (list(self.color),
                [list(e) for e in self.E],
                [list(a) for a in self.adj])

    def restore(self, snap):
        color, E, adj = snap
        self.color = list(color)
        self.E = [list(e) for e in E]
        self.adj = [list(a) for a in adj]

    def add_vertex(self, c):
        self.color.append(c)
        self.adj.append([])
        return len(self.adj) - 1

    def saturate(self, rng):
        """Add edges between opposite-side vertices with spare degree. Never increases distances."""
        d = self.d
        A = [v for v in range(self.n) if self.color[v] == 0 and len(self.adj[v]) < d]
        B = [v for v in range(self.n) if self.color[v] == 1 and len(self.adj[v]) < d]
        rng.shuffle(A)
        rng.shuffle(B)
        for a in A:
            for b in B:
                if len(self.adj[a]) >= d:
                    break
                if len(self.adj[b]) < d and b not in self.adj[a]:
                    self.E.append([a, b])
                    self.adj[a].append(b)
                    self.adj[b].append(a)

    def edges(self):
        return [(a, b) for a, b in self.E]


def _anneal(g, D, deadline, iters, T0, T1, rng):
    """Simulated annealing on degree-preserving or degree-transferring moves; cost = bad pairs."""
    d = g.d
    cost = _bad_pairs(g.n, g.adj, D)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        m = len(g.E)
        if m < 2:
            break
        color = g.color
        if rng.random() < 0.5:
            i = rng.randrange(m)
            a, b = g.E[i]
            if rng.random() < 0.5:
                # Move the A-end of edge i to another A-vertex with spare degree.
                cands = [v for v in range(g.n)
                         if color[v] == 0 and len(g.adj[v]) < d and v not in g.adj[b]]
                if not cands:
                    continue
                x = rng.choice(cands)
                g.replace(i, x, b)
                undo = [(i, a, b)]
            else:
                # Move the B-end of edge i to another B-vertex with spare degree.
                cands = [v for v in range(g.n)
                         if color[v] == 1 and len(g.adj[v]) < d and v not in g.adj[a]]
                if not cands:
                    continue
                y = rng.choice(cands)
                g.replace(i, a, y)
                undo = [(i, a, b)]
        else:
            # Degree-preserving 2-switch.
            i = rng.randrange(m)
            j = rng.randrange(m)
            if i == j:
                continue
            a, b = g.E[i]
            a2, b2 = g.E[j]
            if a == a2 or b == b2 or b2 in g.adj[a] or b in g.adj[a2]:
                continue
            g.replace(i, a, b2)
            g.replace(j, a2, b)
            undo = [(j, a2, b2), (i, a, b)]
        c2 = _bad_pairs(g.n, g.adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            for idx, x, y in undo:
                g.replace(idx, x, y)
    return cost


def _grow_once(g, D, deadline, rng, iters):
    """Add one vertex, attach it with transfers, anneal to diameter D. Keep only on success."""
    d = g.d
    snap = g.snapshot()
    c = rng.randrange(2)
    v = g.add_vertex(c)
    attached = 0
    tries = 0
    while attached < d and tries < 50 * d and g.E:
        tries += 1
        i = rng.randrange(len(g.E))
        a, b = g.E[i]
        if c == 0:
            if len(g.adj[v]) >= d or v in g.adj[b]:
                continue
            g.replace(i, v, b)
        else:
            if len(g.adj[v]) >= d or v in g.adj[a]:
                continue
            g.replace(i, a, v)
        attached += 1
    g.saturate(rng)
    cost = _anneal(g, D, deadline, iters, 1.0, 0.05, rng)
    if cost == 0:
        g.saturate(rng)
        return True
    g.restore(snap)
    return False


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e
    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D.
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # d >= 3, D >= 3: start from the projective plane incidence graph.
    pg = _best_pg(d)
    if pg is None:
        return best_n, best_e
    n0, e0 = pg
    if lib.is_valid(n0, e0, d, D):
        best_n, best_e = n0, e0
    if best_n >= lib.moore_bound(d, D):
        return best_n, best_e

    rng = random.Random(seed)
    m = n0 // 2
    color = [0] * m + [1] * m
    g = _Graph(n0, color, e0, d)
    g.saturate(rng)

    fails = 0
    while time.monotonic() < deadline and fails < 4:
        if _grow_once(g, D, deadline, rng, iters=800):
            fails = 0
            if g.n > best_n:
                cand_e = g.edges()
                if lib.is_valid(g.n, cand_e, d, D):
                    best_n, best_e = g.n, cand_e
                    if best_n >= lib.moore_bound(d, D):
                        break
        else:
            fails += 1

    if not lib.is_valid(best_n, best_e, d, D):
        n0, e0 = pg
        if lib.is_valid(n0, e0, d, D):
            return n0, e0
        return lib.haar_graph(d, range(d))
    return best_n, best_e
