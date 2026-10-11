import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold replacement: local search on bipartite d-regular graphs.
#
# Instead of algebraic lifts, this grows a d-regular bipartite graph one
# vertex pair at a time (warm-started from the previous valid graph) and
# repairs it with double-edge switches. The cost is the number of ordered
# vertex pairs at distance > D, so cost 0 means diameter <= D.
#
# Vertex ids: left vertices are even, right vertices are odd. Ids are always
# 0..N-1, so the output needs no relabelling.
# Every returned graph is checked with lib.is_valid, and the whole search is
# wrapped so that any failure falls back to K_{d,d}.
# ----------------------------------------------------------------------------


def _kdd(d):
    """K_{d,d} with left vertices 2i and right vertices 2j+1. Diameter 2, degree d."""
    return 2 * d, [(2 * i, 2 * j + 1) for i in range(d) for j in range(d)]


class _Graph:
    """Mutable d-regular bipartite graph with edge-set bookkeeping for switches."""

    def __init__(self, d):
        self.d = d
        self.N = 2 * d
        self.adj = [[] for _ in range(self.N)]
        self.E = []
        self.S = set()
        for i in range(d):
            for j in range(d):
                self._add((2 * i, 2 * j + 1))

    def _add(self, e):
        l, r = e
        self.E.append(e)
        self.S.add(e)
        self.adj[l].append(r)
        self.adj[r].append(l)

    def _replace(self, idx, new):
        old = self.E[idx]
        l, r = old
        self.S.discard(old)
        self.adj[l].remove(r)
        self.adj[r].remove(l)
        self.E[idx] = new
        self.S.add(new)
        self.adj[new[0]].append(new[1])
        self.adj[new[1]].append(new[0])

    def cost(self, D):
        """Number of ordered vertex pairs at distance > D (0 means diameter <= D)."""
        N = self.N
        adj = self.adj
        reach = [1 << v for v in range(N)]
        for _ in range(D):
            new = [0] * N
            for v in range(N):
                r = reach[v]
                for u in adj[v]:
                    r |= reach[u]
                new[v] = r
            if new == reach:
                break
            reach = new
        return sum(N - r.bit_count() for r in reach)

    def anneal(self, D, iters, T, deadline, rng):
        """Double-edge-switch annealing. Returns the final cost (0 means success)."""
        c = self.cost(D)
        m = len(self.E)
        for _ in range(iters):
            if c == 0:
                return 0
            if time.monotonic() > deadline:
                break
            i = rng.randrange(m)
            j = rng.randrange(m)
            if i == j:
                continue
            a1, b1 = self.E[i]
            a2, b2 = self.E[j]
            if a1 == a2 or b1 == b2:
                continue
            n1 = (a1, b2)
            n2 = (a2, b1)
            if n1 in self.S or n2 in self.S:
                continue
            self._replace(i, n1)
            self._replace(j, n2)
            c2 = self.cost(D)
            delta = c2 - c
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                c = c2
            else:
                self._replace(j, (a2, b2))
                self._replace(i, (a1, b1))
        return c

    def grow(self, rng):
        """Add one left and one right vertex by subdividing d edges with distinct endpoints.

        Degrees stay exactly d. The result is generally not yet valid, so annealing
        has to repair it afterwards.
        """
        d = self.d
        a = self.N
        b = self.N + 1
        self.adj.append([])
        self.adj.append([])
        self.N += 2
        order = list(range(len(self.E)))
        rng.shuffle(order)
        usedx = set()
        usedy = set()
        picks = []
        for idx in order:
            x, y = self.E[idx]
            if x in usedx or y in usedy:
                continue
            usedx.add(x)
            usedy.add(y)
            picks.append(idx)
            if len(picks) == d:
                break
        if len(picks) < d:
            return False
        for idx in picks:
            x, y = self.E[idx]
            self._replace(idx, (x, b))
            self._add((a, y))
        return True


def _build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    best_n, best_e = _kdd(d)

    # Projective-plane incidence graph is a strong start for D = 3.
    if D >= 3:
        for q in range(min(d - 1, 40), 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                if n > best_n and lib.is_valid(n, e, d, D):
                    best_n, best_e = n, e
                break

    if D < 3 or d < 2:
        return best_n, best_e

    rng = random.Random(seed * 1000003 + d * 31 + D)
    g = _Graph(d)
    while time.monotonic() < deadline:
        T = rng.choice((0.3, 0.6, 0.9))
        c = g.anneal(D, 800, T, deadline, rng)
        if c == 0:
            if g.N > best_n:
                e = list(g.E)
                if lib.is_valid(g.N, e, d, D):
                    best_n, best_e = g.N, e
            if not g.grow(rng):
                break
    return best_n, best_e


def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    try:
        n, e = _build(d, D, seed, time_limit)
        if lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return _kdd(d)
