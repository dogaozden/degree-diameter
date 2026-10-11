import math
import random
import time

import lib


def _pg_fallback(d):
    """Incidence graph of PG(2, d-1) when d-1 is a prime power (Moore-optimal for D = 3)."""
    if d - 1 >= 2 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    return None


def _cost(n, adj, D):
    """Number of unordered vertex pairs at distance greater than D (bitmask balls)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        if new == reach:
            reach = new
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


class _Searcher:
    """Simulated annealing over simple d-regular bipartite graphs with N + N vertices.

    A side vertex a is id a; B side vertex b is id N + b.
    Moves are degree-preserving double-edge swaps. Growth adds one vertex per side
    while keeping every degree equal to d.
    """

    def __init__(self, d, D, rng):
        self.d = d
        self.D = D
        self.rng = rng
        self.N = d
        self.elist = [(a, b) for a in range(d) for b in range(d)]
        self.rebuild()
        self.c = None

    def rebuild(self):
        N = self.N
        self.eset = set(self.elist)
        self.adj = [[] for _ in range(2 * N)]
        for a, b in self.elist:
            self.adj[a].append(N + b)
            self.adj[N + b].append(a)

    def cost(self):
        self.c = _cost(2 * self.N, self.adj, self.D)
        return self.c

    def do_swap(self, i, j):
        """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Self-inverse when applied to the same indices."""
        N = self.N
        a1, b1 = self.elist[i]
        a2, b2 = self.elist[j]
        self.eset.discard((a1, b1))
        self.eset.discard((a2, b2))
        self.eset.add((a1, b2))
        self.eset.add((a2, b1))
        self.elist[i] = (a1, b2)
        self.elist[j] = (a2, b1)
        adj = self.adj
        B1 = N + b1
        B2 = N + b2
        adj[a1][adj[a1].index(B1)] = B2
        adj[a2][adj[a2].index(B2)] = B1
        adj[B1][adj[B1].index(a1)] = a2
        adj[B2][adj[B2].index(a2)] = a1

    def anneal(self, end):
        """Anneal until the cost is zero (return True) or the time `end` is reached (return False)."""
        rng = self.rng
        cost = self.cost()
        if cost == 0:
            return True
        m = len(self.elist)
        t0 = time.monotonic()
        span = max(1e-3, end - t0)
        Thi, Tlo = 4.0, 0.2
        while True:
            now = time.monotonic()
            if now >= end:
                break
            T = Thi * (Tlo / Thi) ** ((now - t0) / span)
            i, j = rng.sample(range(m), 2)
            a1, b1 = self.elist[i]
            a2, b2 = self.elist[j]
            if a1 == a2 or b1 == b2:
                continue
            if (a1, b2) in self.eset or (a2, b1) in self.eset:
                continue
            self.do_swap(i, j)
            c2 = self.cost()
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
                if cost == 0:
                    return True
            else:
                self.do_swap(i, j)
        self.c = cost
        return False

    def grow(self):
        """Add one A vertex and one B vertex, keeping d-regularity.

        Pick d disjoint edges (x_i, y_i). Remove them, then join the new B vertex to every x_i
        and the new A vertex to every y_i. Returns False if no such matching is found.
        """
        rng = self.rng
        d = self.d
        N = self.N
        idx = list(range(len(self.elist)))
        rng.shuffle(idx)
        usedA, usedB, chosen = set(), set(), []
        for i in idx:
            a, b = self.elist[i]
            if a in usedA or b in usedB:
                continue
            usedA.add(a)
            usedB.add(b)
            chosen.append(i)
            if len(chosen) == d:
                break
        if len(chosen) < d:
            return False
        ch = set(chosen)
        new = [e for i, e in enumerate(self.elist) if i not in ch]
        for i in chosen:
            x, y = self.elist[i]
            new.append((x, N))   # old A vertex x joins new B vertex N
            new.append((N, y))   # new A vertex N joins old B vertex y
        self.N = N + 1
        self.elist = new
        self.rebuild()
        return True

    def edges_list(self):
        N = self.N
        return [(a, N + b) for a, b in self.elist]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    pg = _pg_fallback(d)
    if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
        if pg[0] > best[0]:
            best = pg
        if D == 3:
            return best

    best_n = best[0]
    bound = 2 * sum((d - 1) ** i for i in range(D))

    try:
        S = _Searcher(d, D, rng)
        while time.monotonic() < deadline:
            ok = S.anneal(min(deadline, time.monotonic() + 3.0))
            if not ok:
                continue
            n = 2 * S.N
            if n > best_n:
                e = S.edges_list()
                if lib.is_valid(n, e, d, D):
                    best = (n, e)
                    best_n = n
            if 2 * (S.N + 1) > bound:
                break
            if not S.grow():
                break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
