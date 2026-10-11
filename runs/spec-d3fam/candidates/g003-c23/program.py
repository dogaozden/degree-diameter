import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Base constructions (safe fallbacks).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _ara(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2, q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


# ----------------------------------------------------------------------------
# Bipartite local search with diameter-penalty cost.
#
# State: bipartite graph with sides 0/1, degree <= d, edge list E of pairs
# (a, b) with side[a] == 0 and side[b] == 1, and a dense adjacency matrix A.
# Cost = number of ordered vertex pairs at distance > D (zero means valid).
# Moves keep the bipartition and degree bound: double-edge swaps, endpoint
# rewiring to deficient vertices, and adding edges between deficient vertices.
# Growth adds one vertex per side by stealing edges, then refills degrees.
# ----------------------------------------------------------------------------

class _Bi:
    def __init__(self, n, edges, side, d):
        self.n = n
        self.d = d
        self.side = list(side)
        self.E = []
        self.A = np.zeros((n, n), dtype=np.float32)
        self.deg = [0] * n
        for u, v in edges:
            a, b = (u, v) if self.side[u] == 0 else (v, u)
            self.E.append([a, b])
            self.A[a, b] = 1
            self.A[b, a] = 1
            self.deg[a] += 1
            self.deg[b] += 1

    def set_edge(self, a, b, val):
        self.A[a, b] = val
        self.A[b, a] = val

    def deficient(self, s):
        return [v for v in range(self.n) if self.side[v] == s and self.deg[v] < self.d]

    def bad(self, D):
        """Number of ordered pairs at distance > D (unreachable pairs included)."""
        M = self.A.copy()
        np.fill_diagonal(M, 1.0)
        P = M
        for _ in range(D - 1):
            P = np.minimum(P @ M, 1.0)  # clamp keeps values boolean-like and avoids overflow
        return self.n * self.n - int(np.count_nonzero(P))

    def move(self, rng):
        """Apply a random move; return an undo closure, or None if the move was not applicable."""
        E = self.E
        m = len(E)
        r = rng.random()
        if r < 0.6:
            if m < 2:
                return None
            i = rng.randrange(m)
            j = rng.randrange(m)
            if i == j:
                return None
            a, b = E[i]
            c, e = E[j]
            if a == c or b == e:
                return None
            if self.A[a, e] or self.A[c, b]:
                return None
            self.set_edge(a, b, 0)
            self.set_edge(c, e, 0)
            self.set_edge(a, e, 1)
            self.set_edge(c, b, 1)
            E[i] = [a, e]
            E[j] = [c, b]

            def undo():
                self.set_edge(a, e, 0)
                self.set_edge(c, b, 0)
                self.set_edge(a, b, 1)
                self.set_edge(c, e, 1)
                E[i] = [a, b]
                E[j] = [c, e]
            return undo

        if r < 0.8:
            # Move the side-0 endpoint of an edge to a deficient side-0 vertex.
            if m == 0:
                return None
            i = rng.randrange(m)
            a, b = E[i]
            cand = self.deficient(0)
            if not cand:
                return None
            x = rng.choice(cand)
            if x == a or self.A[x, b]:
                return None
            self.set_edge(a, b, 0)
            self.set_edge(x, b, 1)
            E[i] = [x, b]
            self.deg[a] -= 1
            self.deg[x] += 1

            def undo():
                self.set_edge(x, b, 0)
                self.set_edge(a, b, 1)
                E[i] = [a, b]
                self.deg[a] += 1
                self.deg[x] -= 1
            return undo

        if r < 0.9:
            # Move the side-1 endpoint of an edge to a deficient side-1 vertex.
            if m == 0:
                return None
            i = rng.randrange(m)
            a, b = E[i]
            cand = self.deficient(1)
            if not cand:
                return None
            y = rng.choice(cand)
            if y == b or self.A[a, y]:
                return None
            self.set_edge(a, b, 0)
            self.set_edge(a, y, 1)
            E[i] = [a, y]
            self.deg[b] -= 1
            self.deg[y] += 1

            def undo():
                self.set_edge(a, y, 0)
                self.set_edge(a, b, 1)
                E[i] = [a, b]
                self.deg[b] += 1
                self.deg[y] -= 1
            return undo

        # Add an edge between two deficient vertices on opposite sides.
        c0 = self.deficient(0)
        c1 = self.deficient(1)
        if not c0 or not c1:
            return None
        a = rng.choice(c0)
        b = rng.choice(c1)
        if self.A[a, b]:
            return None
        self.set_edge(a, b, 1)
        E.append([a, b])
        self.deg[a] += 1
        self.deg[b] += 1

        def undo():
            self.set_edge(a, b, 0)
            E.pop()
            self.deg[a] -= 1
            self.deg[b] -= 1
        return undo

    def fill(self, rng):
        """Greedily add edges between deficient opposite-side vertices."""
        c0 = self.deficient(0)
        c1 = self.deficient(1)
        rng.shuffle(c0)
        rng.shuffle(c1)
        for a in c0:
            for b in c1:
                if self.deg[a] >= self.d:
                    break
                if self.deg[b] < self.d and not self.A[a, b]:
                    self.set_edge(a, b, 1)
                    self.E.append([a, b])
                    self.deg[a] += 1
                    self.deg[b] += 1

    def extend(self, rng):
        """Add one vertex per side; each takes d edges by stealing from random edges, then refill."""
        d = self.d
        n = self.n
        N = n + 2
        A2 = np.zeros((N, N), dtype=np.float32)
        A2[:n, :n] = self.A
        self.A = A2
        self.n = N
        self.side += [0, 1]
        self.deg += [0, 0]
        x, y = n, n + 1
        for v, s in ((x, 0), (y, 1)):
            added = 0
            tries = 0
            while added < d and tries < 50 * d and self.E:
                tries += 1
                i = rng.randrange(len(self.E))
                a, b = self.E[i]
                if s == 0:
                    if self.A[v, b]:
                        continue
                    self.set_edge(a, b, 0)
                    self.set_edge(v, b, 1)
                    self.E[i] = [v, b]
                    self.deg[a] -= 1
                else:
                    if self.A[a, v]:
                        continue
                    self.set_edge(a, b, 0)
                    self.set_edge(a, v, 1)
                    self.E[i] = [a, v]
                    self.deg[b] -= 1
                self.deg[v] += 1
                added += 1
        self.fill(rng)


def _anneal(st, D, deadline, rng, record):
    """Simulated annealing; whenever the cost hits zero, record the graph and grow by one pair."""
    SEG = 600
    cur = st.bad(D)
    k = 0
    while time.monotonic() < deadline:
        if cur == 0:
            record(st)
            st.extend(rng)
            cur = st.bad(D)
            k = 0
            continue
        T = 3.0 * (0.03 ** (k / SEG))
        k += 1
        if k >= SEG:
            k = 0
        undo = st.move(rng)
        if undo is None:
            continue
        new = st.bad(D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            undo()


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 0.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D}: diameter D, degree 2, bipartite.
        N = 2 * D
        return N, [(i, (i + 1) % N) for i in range(N)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D < 3:
        return best

    # Known constructions.
    ara = _ara(d)
    if ara is not None:
        consider(ara[0], ara[1])
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Bold change for D >= 3: local search on a bipartite graph seeded from the
    # best construction, growing it one vertex pair at a time whenever the
    # diameter cost reaches zero.
    if best_n >= lib._moore_bound(d, D):
        return best

    base_n, base_e = best
    adj = lib.adjacency(base_n, base_e)
    side = _bipartition(base_n, adj)
    st = _Bi(base_n, base_e, side, d)

    found = [best]

    def record(s):
        if s.n > found[0][0]:
            edges = [(int(a), int(b)) for a, b in s.E]
            if lib.is_valid(s.n, edges, d, D):
                found[0] = (s.n, edges)

    _anneal(st, D, deadline, rng, record)

    n, e = found[0]
    if lib.is_valid(n, e, d, D):
        return n, e
    return lib.haar_graph(d, range(d))
