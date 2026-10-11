import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Edge-switch simulated annealing on bipartite graphs with max degree d.
#
# Each state is a bipartite graph (sides 0 and 1) with max degree d. The cost
# is the number of unordered vertex pairs at distance > D, so zero means valid.
# Growth: add one vertex per side, then anneal until the cost returns to zero.
# Moves preserve bipartiteness and the degree cap. Adding edges between
# deficient opposite-side vertices never increases the cost, so it is applied
# greedily after every accepted move.
# ----------------------------------------------------------------------------

def _cost(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
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


class _Graph:
    def __init__(self, n, side, edges, d):
        self.n = n
        self.side = list(side)
        self.d = d
        self.adj = [set() for _ in range(n)]
        for u, v in edges:
            self.adj[u].add(v)
            self.adj[v].add(u)
        self.L = [v for v in range(n) if self.side[v] == 0]
        self.R = [v for v in range(n) if self.side[v] == 1]

    def add_pair(self):
        a, b = self.n, self.n + 1
        self.n += 2
        self.side += [0, 1]
        self.adj.append(set())
        self.adj.append(set())
        self.L.append(a)
        self.R.append(b)

    def add_e(self, a, b):
        self.adj[a].add(b)
        self.adj[b].add(a)

    def rem_e(self, a, b):
        self.adj[a].discard(b)
        self.adj[b].discard(a)

    def fill(self, rng):
        """Greedily join deficient left-right pairs; returns number of edges added."""
        dl = [v for v in self.L if len(self.adj[v]) < self.d]
        dr = [v for v in self.R if len(self.adj[v]) < self.d]
        rng.shuffle(dl)
        rng.shuffle(dr)
        added = 0
        for a in dl:
            for b in dr:
                if len(self.adj[a]) >= self.d:
                    break
                if len(self.adj[b]) < self.d and b not in self.adj[a]:
                    self.add_e(a, b)
                    added += 1
        return added

    def edges(self):
        return [(u, v) for u in range(self.n) for v in self.adj[u] if u < v]


def _move(g, rng):
    """Propose a degree-safe move as a list of ('add'|'rem', x, y) ops, or None."""
    d = g.d
    adj = g.adj
    a = rng.choice(g.L)
    if not adj[a]:
        return None
    b = rng.choice(tuple(adj[a]))
    r = rng.random()
    if r < 0.6:
        # Switch: (a,b),(c,e) -> (a,e),(c,b)
        c = rng.choice(g.L)
        if c == a or not adj[c]:
            return None
        e = rng.choice(tuple(adj[c]))
        if e == b or e in adj[a] or b in adj[c]:
            return None
        return [('rem', a, b), ('rem', c, e), ('add', a, e), ('add', c, b)]
    if r < 0.8:
        # Move right endpoint of (a,b) to a deficient right vertex e.
        dr = [v for v in g.R if len(adj[v]) < d]
        if not dr:
            return None
        e = rng.choice(dr)
        if e == b or e in adj[a]:
            return None
        return [('rem', a, b), ('add', a, e)]
    # Move left endpoint of (a,b) to a deficient left vertex c.
    dl = [v for v in g.L if len(adj[v]) < d]
    if not dl:
        return None
    c = rng.choice(dl)
    if c == a or c in adj[b]:
        return None
    return [('rem', a, b), ('add', c, b)]


def _apply(g, ops):
    for op, x, y in ops:
        if op == 'add':
            g.add_e(x, y)
        else:
            g.rem_e(x, y)


def _undo(g, ops):
    for op, x, y in reversed(ops):
        if op == 'add':
            g.rem_e(x, y)
        else:
            g.add_e(x, y)


def _anneal(g, D, rng, deadline):
    """Anneal until the cost is zero; returns True on success, False at the deadline."""
    g.fill(rng)
    cost = _cost(g.n, g.adj, D)
    T = 0.6
    while cost > 0:
        if time.monotonic() > deadline:
            return False
        ops = _move(g, rng)
        if ops is None:
            continue
        _apply(g, ops)
        c2 = _cost(g.n, g.adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
            cost = c2
            if g.fill(rng):
                cost = _cost(g.n, g.adj, D)
        else:
            _undo(g, ops)
    return True


def _from_edges(n, edges):
    """Recover a side labelling for a bipartite graph by BFS 2-colouring."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.80 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        # Structured baseline: projective plane incidence when d-1 is a prime power.
        if D >= 3 and 2 <= d - 1 <= 23 and lib.is_prime_power(d - 1):
            n0, e0 = lib.projective_plane_incidence(d - 1)
            consider(n0, e0)

        # Grow the best valid graph by SA-based vertex addition.
        if D >= 3 and d >= 2 and time.monotonic() < deadline:
            rng = random.Random(seed * 1000003 + d * 101 + D)
            n0, e0 = best
            side = _from_edges(n0, e0)
            g = _Graph(n0, side, e0, d)
            while time.monotonic() < deadline:
                if g.n + 2 > lib.moore_bound(d, D):
                    break
                g.add_pair()
                if not _anneal(g, D, rng, deadline):
                    break
                consider(g.n, g.edges())
    except Exception:
        pass  # keep the best valid graph found so far

    n, edges = best
    if not lib.is_valid(n, edges, d, D):
        return lib.haar_graph(d, range(d))
    return n, edges
