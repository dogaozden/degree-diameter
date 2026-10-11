import math
import random
import time

import lib


def _pg_incidence(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _regular(n, edges, d):
    """True if every vertex 0..n-1 has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


def _bit_cost(n, adj, D):
    """Ordered count of (vertex, vertex) pairs at distance > D; zero iff diameter <= D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


class _Lift:
    """Bipartite graph kept as an edge list [a, b] (a on side A, b on side B).

    Moves preserve every vertex degree: a 2-switch replaces (a1,b1),(a2,b2)
    with (a1,b2),(a2,b1); an expansion adds one A and one B vertex of degree d
    by splitting a matching of d edges.
    """

    def __init__(self, V, edges):
        self.V = V
        self.el = [[a, b] for a, b in edges]
        self.es = set((a, b) for a, b in self.el)
        self.adj = [[] for _ in range(V)]
        for a, b in self.el:
            self.adj[a].append(b)
            self.adj[b].append(a)

    def cost(self, D):
        return _bit_cost(self.V, self.adj, D)

    def switch(self, i, j):
        """2-switch on edge slots i and j. Calling it again on the same slots undoes it."""
        el, es, adj = self.el, self.es, self.adj
        a1, b1 = el[i]
        a2, b2 = el[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in es or (a2, b1) in es:
            return False
        es.discard((a1, b1))
        es.discard((a2, b2))
        es.add((a1, b2))
        es.add((a2, b1))
        adj[a1].remove(b1)
        adj[b1].remove(a1)
        adj[a2].remove(b2)
        adj[b2].remove(a2)
        adj[a1].append(b2)
        adj[b2].append(a1)
        adj[a2].append(b1)
        adj[b1].append(a2)
        el[i] = [a1, b2]
        el[j] = [a2, b1]
        return True

    def expand(self, d, rng):
        """Add one A vertex and one B vertex, both of degree d; all degrees stay d."""
        el, es, adj = self.el, self.es, self.adj
        order = list(range(len(el)))
        rng.shuffle(order)
        usedA, usedB, chosen = set(), set(), []
        for k in order:
            a, b = el[k]
            if a in usedA or b in usedB:
                continue
            usedA.add(a)
            usedB.add(b)
            chosen.append(k)
            if len(chosen) == d:
                break
        if len(chosen) < d:
            return False
        na, nb = self.V, self.V + 1
        self.V += 2
        adj.append([])
        adj.append([])
        ends = [(k, el[k][0], el[k][1]) for k in chosen]
        for k, a, b in ends:
            es.discard((a, b))
            adj[a].remove(b)
            adj[b].remove(a)
            # slot k becomes (na, b)
            el[k] = [na, b]
            es.add((na, b))
            adj[na].append(b)
            adj[b].append(na)
            # new slot (a, nb)
            el.append([a, nb])
            es.add((a, nb))
            adj[a].append(nb)
            adj[nb].append(a)
        return True

    def anneal(self, D, deadline, rng, max_iters):
        """Random 2-switches with Metropolis acceptance. Returns the final cost (0 = success)."""
        cur = self.cost(D)
        m = len(self.el)
        T = 2.0
        it = 0
        while cur > 0 and it < max_iters and time.monotonic() < deadline:
            it += 1
            T = max(0.25, T * 0.9993)
            i = rng.randrange(m)
            j = rng.randrange(m)
            if i == j or not self.switch(i, j):
                continue
            new = self.cost(D)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
            else:
                self.switch(i, j)
        return cur


def _grow(d, D, deadline, rng, V0, edges0):
    """Repeatedly add a vertex pair to a valid d-regular bipartite graph, then re-anneal to diameter D.

    On failure the state rolls back to the last valid graph. Returns the best valid (V, edges).
    """
    best_V, best_edges = V0, list(edges0)
    cur = _Lift(V0, edges0)
    fails = 0
    while fails < 6:
        now = time.monotonic()
        if now >= deadline:
            break
        snap_V = cur.V
        snap_el = [list(e) for e in cur.el]
        if not cur.expand(d, rng):
            break
        slice_end = min(deadline, now + 3.0 * (2 ** fails))
        c = cur.anneal(D, slice_end, rng, 10 ** 9)
        ok = False
        if c == 0:
            edges = [(a, b) for a, b in cur.el]
            if lib.is_valid(cur.V, edges, d, D):
                ok = True
                best_V, best_edges = cur.V, edges
        if ok:
            fails = 0
        else:
            fails += 1
            cur = _Lift(snap_V, snap_el)
    return best_V, best_edges


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is d-regular.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    cands = [fallback]
    for g in (_pg_incidence(d), _araujo(d)):
        if g is not None and lib.is_valid(g[0], g[1], d, D):
            cands.append(g)

    if D == 3:
        best = max(cands, key=lambda g: g[0])
        return best[0], list(best[1])

    # D >= 4: grow a d-regular start by vertex-pair insertion plus annealed 2-switches.
    regular = [g for g in cands if _regular(g[0], g[1], d)]
    start = max(regular, key=lambda g: g[0])
    V, E = _grow(d, D, deadline, rng, start[0], start[1])
    if lib.is_valid(V, E, d, D):
        return V, E
    return fallback
