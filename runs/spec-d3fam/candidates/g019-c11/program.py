import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions (validated before use).
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
# Fast bad-pair count: pairs at distance > D (unreachable pairs included).
# ----------------------------------------------------------------------------

def _popcount(x):
    return x.bit_count() if hasattr(x, "bit_count") else bin(x).count("1")


def _bad(n, adj, D):
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - _popcount(r) for r in reach) // 2


def _color(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


# ----------------------------------------------------------------------------
# Bipartite graph state with degree-bounded local moves.
#
# Moves keep the graph bipartite and simple and never exceed degree d:
#   shift:  move one endpoint of an edge to a deficient vertex on the same side,
#   switch: degree-preserving double edge swap,
#   add:    join two non-adjacent deficient vertices on opposite sides.
# ----------------------------------------------------------------------------

class _Graph:
    def __init__(self, n, edges, d, D, rng):
        self.d, self.D, self.rng = d, D, rng
        self.n = n
        self.adj = [set() for _ in range(n)]
        for u, v in edges:
            self.adj[u].add(v)
            self.adj[v].add(u)
        self.col = _color(n, [list(s) for s in self.adj])
        self.E = [self._pair(u, v) for u, v in edges]

    def _pair(self, u, v):
        return (u, v) if self.col[u] == 0 else (v, u)

    def _link(self, a, b):
        # a is on side 0, b on side 1; the edge must be new.
        self.E.append((a, b))
        self.adj[a].add(b)
        self.adj[b].add(a)

    def _unlink_last(self):
        a, b = self.E.pop()
        self.adj[a].discard(b)
        self.adj[b].discard(a)

    def _swap_edge(self, i, a2, b2):
        a, b = self.E[i]
        self.adj[a].discard(b)
        self.adj[b].discard(a)
        self.adj[a2].add(b2)
        self.adj[b2].add(a2)
        self.E[i] = (a2, b2)

    def _deficient(self):
        return [v for v in range(self.n) if len(self.adj[v]) < self.d]

    def add_vertex(self, c):
        v = self.n
        self.n += 1
        self.adj.append(set())
        self.col.append(c)
        opp = [u for u in range(v) if self.col[u] != c and len(self.adj[u]) < self.d]
        self.rng.shuffle(opp)
        for u in opp[:self.d]:
            self._link(*self._pair(u, v))

    def fill(self):
        A = [v for v in range(self.n) if self.col[v] == 0 and len(self.adj[v]) < self.d]
        B = [v for v in range(self.n) if self.col[v] == 1 and len(self.adj[v]) < self.d]
        self.rng.shuffle(A)
        self.rng.shuffle(B)
        for a in A:
            for b in B:
                if len(self.adj[a]) >= self.d:
                    break
                if len(self.adj[b]) < self.d and b not in self.adj[a]:
                    self._link(a, b)

    def propose(self):
        """Apply a random move; return an undo callable, or None if the move was not legal."""
        rng = self.rng
        m = len(self.E)
        r = rng.random()
        defi = self._deficient()

        if r < 0.15:
            A = [v for v in defi if self.col[v] == 0]
            B = [v for v in defi if self.col[v] == 1]
            if A and B:
                a = rng.choice(A)
                b = rng.choice(B)
                if b not in self.adj[a]:
                    self._link(a, b)
                    return self._unlink_last
            return None

        if r < 0.55 and defi and m:
            v = rng.choice(defi)
            i = rng.randrange(m)
            a, b = self.E[i]
            if self.col[v] == 0:
                if v == a or v in self.adj[b]:
                    return None
                self._swap_edge(i, v, b)
            else:
                if v == b or v in self.adj[a]:
                    return None
                self._swap_edge(i, a, v)
            return lambda: self._swap_edge(i, a, b)

        if m < 2:
            return None
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            return None
        a, b = self.E[i]
        c, e = self.E[j]
        if a == c or b == e or e in self.adj[a] or b in self.adj[c]:
            return None
        self._swap_edge(i, a, e)
        self._swap_edge(j, c, b)

        def undo():
            self._swap_edge(j, c, e)
            self._swap_edge(i, a, b)

        return undo


def _anneal(g, iters, T0, T1, deadline):
    """Simulated annealing on the bad-pair count. Returns the final cost (0 = valid)."""
    cost = _bad(g.n, g.adj, g.D)
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        undo = g.propose()
        if undo is None:
            continue
        c2 = _bad(g.n, g.adj, g.D)
        delta = c2 - cost
        if delta <= 0 or g.rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            undo()
    return cost


# ----------------------------------------------------------------------------
# Main entry point.
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

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        rec = _araujo(d)
        if rec is not None:
            consider(rec[0], rec[1])
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Bold search: grow the best known graph by one vertex at a time, then
    # repair it by annealing over degree-bounded bipartite moves. Any repaired
    # graph of larger order replaces the incumbent; failed attempts restart
    # from the incumbent.
    g = _Graph(best[0], best[1], d, D, rng)
    attempt_budget = max(2.0, 0.2 * time_limit)
    while time.monotonic() < deadline:
        cnt0 = sum(1 for c in g.col if c == 0)
        cnt1 = len(g.col) - cnt0
        c0 = 0 if cnt0 <= cnt1 else 1
        g.add_vertex(c0)
        g.fill()

        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        budget = min(remaining, attempt_budget)
        cost = _anneal(g, 3000, 1.5, 0.05, time.monotonic() + budget)

        if cost == 0 and g.n > best[0] and lib.is_valid(g.n, list(g.E), d, D):
            best = (g.n, list(g.E))
        else:
            g = _Graph(best[0], best[1], d, D, rng)

    n, e = best
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
