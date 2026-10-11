import math
import random
import time

import lib


def _key(a, b):
    return (a, b) if a < b else (b, a)


def _cycle(D):
    n = 2 * D
    return n, [(i, (i + 1) % n) for i in range(n)]


def _bipartition(n, edges):
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


def _base_candidates(d, D):
    cands = [lib.haar_graph(d, range(d))]  # K_{d,d}, diameter 2
    if D >= 3:
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                cands.append(lib.projective_plane_incidence(q))
                break
    return cands


class _Graph:
    """Mutable bipartite graph with degree cap d; ops are (0, u, v) remove or (1, u, v) add."""

    def __init__(self, n, edges, color, d):
        self.n = n
        self.d = d
        self.adj = [[] for _ in range(n)]
        self.E = set()
        self.color = list(color)
        for u, v in edges:
            self.add(u, v)

    def add(self, u, v):
        self.adj[u].append(v)
        self.adj[v].append(u)
        self.E.add(_key(u, v))

    def rem(self, u, v):
        self.adj[u].remove(v)
        self.adj[v].remove(u)
        self.E.discard(_key(u, v))

    def add_vertex(self, c):
        self.adj.append([])
        self.color.append(c)
        self.n += 1
        return self.n - 1

    def apply(self, ops):
        for op, u, v in ops:
            if op == 0:
                self.rem(u, v)
            else:
                self.add(u, v)

    def revert(self, ops):
        for op, u, v in reversed(ops):
            if op == 0:
                self.add(u, v)
            else:
                self.rem(u, v)

    def deficit(self, c):
        return [v for v in range(self.n)
                if self.color[v] == c and len(self.adj[v]) < self.d]

    def edge_list(self):
        return [(u, v) for u in range(self.n) for v in self.adj[u] if u < v]


def _cost(n, adj, D):
    """Ordered pairs at distance > D (including unreachable). Zero iff diameter <= D and connected."""
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


def _move(G, rng):
    """Propose a degree-respecting move as a list of ops (not applied), or None."""
    n = G.n
    nz = [v for v in range(n) if G.adj[v]]
    if not nz:
        return None
    r = rng.random()
    if r < 0.3:
        # Add an edge between two deficient, non-adjacent opposite-side vertices.
        A = G.deficit(0)
        B = G.deficit(1)
        if not A or not B:
            return None
        a = rng.choice(A)
        b = rng.choice(B)
        if _key(a, b) in G.E:
            return None
        return [(1, a, b)]
    x = rng.choice(nz)
    y = rng.choice(G.adj[x])
    if r < 0.6:
        # Shift: move endpoint of edge (x, y) from x to a deficient same-side vertex.
        cand = [v for v in G.deficit(G.color[x])
                if v != x and _key(v, y) not in G.E]
        if not cand:
            return None
        xp = rng.choice(cand)
        return [(0, x, y), (1, xp, y)]
    # Double edge swap, preserving all degrees and bipartiteness.
    same = [v for v in nz if G.color[v] == G.color[x] and v != x]
    if not same:
        return None
    x2 = rng.choice(same)
    y2 = rng.choice(G.adj[x2])
    if y2 == y or _key(x, y2) in G.E or _key(x2, y) in G.E:
        return None
    return [(0, x, y), (0, x2, y2), (1, x, y2), (1, x2, y)]


def _anneal(G, D, rng, deadline):
    """Metropolis search over moves until cost 0 or deadline. Returns final cost."""
    cur = _cost(G.n, G.adj, D)
    t0 = time.monotonic()
    span = max(deadline - t0, 1e-3)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 1.5 * (0.03 ** ((now - t0) / span))
        ops = _move(G, rng)
        if ops is None:
            continue
        G.apply(ops)
        new = _cost(G.n, G.adj, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            G.revert(ops)
    return cur


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.3 * time_limit, min(0.8 * time_limit, time_limit - 6))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        return _cycle(D)

    # Safe starting point: best valid base among the known constructions.
    cands = [c for c in _base_candidates(d, D) if lib.is_valid(c[0], c[1], d, D)]
    if not cands:
        return lib.haar_graph(d, range(d))
    best_n, best_e = max(cands, key=lambda c: c[0])

    # Growth: add one A/B vertex pair, then repair with degree-preserving search.
    # On failure, restart from the last valid graph with fresh randomness.
    while time.monotonic() < deadline - 0.5:
        remaining = deadline - time.monotonic()
        G = _Graph(best_n, best_e, _bipartition(best_n, best_e), d)
        G.add_vertex(0)
        G.add_vertex(1)
        budget_end = time.monotonic() + 0.5 * remaining
        cost = _anneal(G, D, rng, budget_end)
        if cost == 0:
            edges = G.edge_list()
            if lib.is_valid(G.n, edges, d, D):
                best_n, best_e = G.n, edges

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
