"""Graph builder for bipartite max-degree d, diameter <= D.

Pipeline:
  1. Baselines: K_{d,d} (diameter 2) and the incidence graph of PG(2, q).
  2. Annealed bi-Cayley voltage lifts over Z_m x| Z_k (group-lift search).
  3. NEW: diameter-repair growth. Start from the best valid graph and add one
     A-vertex and one B-vertex. Then anneal over degree-aware edge moves
     (degree-preserving 2-swaps and endpoint relocations into spare degree),
     with a greedy saturation fill after each move. The cost is the number of
     ordered vertex pairs at distance > D, computed with big-int bitsets.
     Each success grows the graph by one A/B pair and repeats.
"""
import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Baselines
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
# Bi-Cayley voltage lifts over Z_m x| Z_k (annealed)
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _lift_cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _lift_anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)
    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    start = time.monotonic()
    span = max(1e-3, deadline - start)

    for _ in range(iters):
        now = time.monotonic()
        if cost == 0 or now > deadline:
            break
        T = max(0.5, T0 * (1.0 - (now - start) / span))
        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _lift_cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _lift_cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _lift_edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# NEW: diameter-repair growth with degree-aware edge moves
# ----------------------------------------------------------------------------

def _bit_cost(n, adj, D):
    """Sum over vertices of the number of vertices at distance > D (bitset BFS)."""
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


class _Rep:
    """Bipartite graph state with degree cap d, supporting logged edits and undo."""

    def __init__(self, n, color, d, edges):
        self.n = n
        self.d = d
        self.color = list(color)
        self.adj = [set() for _ in range(n)]
        self.deg = [0] * n
        self.el = []
        self.log = None
        self.side0 = [v for v in range(n) if color[v] == 0]
        self.side1 = [v for v in range(n) if color[v] == 1]
        for a, b in edges:
            if color[a] == 0:
                self._raw_add(a, b)
            else:
                self._raw_add(b, a)

    def _raw_add(self, a, b):
        self.adj[a].add(b)
        self.adj[b].add(a)
        self.deg[a] += 1
        self.deg[b] += 1
        self.el.append((a, b))

    def _raw_rem(self, a, b):
        self.adj[a].discard(b)
        self.adj[b].discard(a)
        self.deg[a] -= 1
        self.deg[b] -= 1
        self.el.remove((a, b))

    def add(self, a, b):
        self._raw_add(a, b)
        if self.log is not None:
            self.log.append((1, a, b))

    def rem(self, a, b):
        self._raw_rem(a, b)
        if self.log is not None:
            self.log.append((-1, a, b))

    def undo(self):
        for op, a, b in reversed(self.log):
            if op == 1:
                self._raw_rem(a, b)
            else:
                self._raw_add(a, b)

    def grow_pair(self):
        x, y = self.n, self.n + 1
        self.n += 2
        self.color += [0, 1]
        self.adj += [set(), set()]
        self.deg += [0, 0]
        self.side0.append(x)
        self.side1.append(y)

    def fill(self, rng):
        """Greedily add missing A-B edges between deficient vertices (never hurts distances)."""
        d = self.d
        left = [v for v in self.side0 if self.deg[v] < d]
        right = [v for v in self.side1 if self.deg[v] < d]
        rng.shuffle(left)
        rng.shuffle(right)
        for a in left:
            if self.deg[a] >= d:
                continue
            for b in right:
                if self.deg[b] >= d or self.deg[a] >= d:
                    if self.deg[a] >= d:
                        break
                    continue
                if b not in self.adj[a]:
                    self.add(a, b)

    def cost(self, D):
        return _bit_cost(self.n, self.adj, D)


def _anneal_rep(st, D, deadline, rng):
    """Anneal the state toward zero bad pairs. Returns True on success."""
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    cost = st.cost(D)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline or len(st.el) < 2:
            break
        T = max(0.25, 2.0 * (1.0 - (now - start) / span))
        st.log = []
        if rng.random() < 0.6:
            (a1, b1), (a2, b2) = rng.sample(st.el, 2)
            if a1 == a2 or b1 == b2 or b2 in st.adj[a1] or b1 in st.adj[a2]:
                st.log = None
                continue
            st.rem(a1, b1)
            st.rem(a2, b2)
            st.add(a1, b2)
            st.add(a2, b1)
        else:
            a, b = rng.choice(st.el)
            if rng.random() < 0.5:
                cands = [x for x in st.side0
                         if st.deg[x] < st.d and x != a and x not in st.adj[b]]
                if not cands:
                    st.log = None
                    continue
                x = rng.choice(cands)
                st.rem(a, b)
                st.add(x, b)
            else:
                cands = [y for y in st.side1
                         if st.deg[y] < st.d and y != b and y not in st.adj[a]]
                if not cands:
                    st.log = None
                    continue
                y = rng.choice(cands)
                st.rem(a, b)
                st.add(a, y)
        st.fill(rng)
        c2 = st.cost(D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            st.undo()
        st.log = None
    return cost == 0


def _repair_grow(best_n, best_e, d, D, deadline, rng, consider):
    """Repeatedly add an A/B pair and anneal back to diameter <= D."""
    adj = [[] for _ in range(best_n)]
    for u, v in best_e:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(best_n, adj)
    st = _Rep(best_n, color, d, best_e)
    st.fill(rng)
    while time.monotonic() < deadline:
        if not _anneal_rep(st, D, deadline, rng):
            break
        consider(st.n, list(st.el))
        st.grow_pair()
        st.fill(rng)


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, list(e))
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Phase 1: annealed group lifts.
    lift_frac = 0.4 if D >= 5 else 0.6
    lift_end = start + lift_frac * 0.8 * time_limit
    if D >= 5:
        ks, iters = [1, 1, 2, 2, 3, 4], 1500
    else:
        ks, iters = [1, 1, 2, 3], 400
    while time.monotonic() < lift_end:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        if D >= 5:
            G = max(2, base + 1 + rng.randrange(0, 3))
        else:
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _lift_anneal(d, D, k, order, mul, rng, lift_end, iters)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2: NEW diameter-repair growth from the best graph found so far.
    if time.monotonic() < deadline:
        _repair_grow(best[0], best[1], d, D, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
