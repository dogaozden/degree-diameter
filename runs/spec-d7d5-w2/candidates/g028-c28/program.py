import itertools
import math
import random
import time

import numpy as np

import lib


# Shift used to encode an edge (a, b) as one integer key. Vertex counts stay far below this.
_SH = 1 << 21
_PENALTY = 1000
_KS = (1, 2, 3, 4)


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (phase 1).
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach_np(k, G, D, nbr, d):
    """Bitmask per vertex: bit b is set when representative block b is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _unreached(k, N, reach):
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over voltages, layer swaps and defect-targeted moves. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach_np(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach_np(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach_np(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Bipartition colouring.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Return a proper 2-colouring (list of 0/1) of the graph, or None if it is not bipartite."""
    adj = lib.adjacency(n, edges)
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


# ----------------------------------------------------------------------------
# Phase 2 (new): bipartite edge-switch annealing with vertex-pair growth.
#
# The graph is kept bipartite and d-regular at all times. Moves are
# "switches": edges (a1,b1),(a2,b2) become (a1,b2),(a2,b1). Switches keep
# every degree and the bipartition, so validity only depends on diameter.
# A growth step adds two vertices x (side 0), y (side 1) and the edge x-y,
# re-attaching d-1 removed edges; the annealer then repairs the diameter.
# ----------------------------------------------------------------------------

class _Graph:
    """Mutable bipartite graph with edge list, position index and adjacency lists."""

    def __init__(self, n, edges, color):
        self.n = n
        self.color = color
        self.adj = [[] for _ in range(n)]
        self.E = []
        self.pos = {}
        for u, v in edges:
            a, b = (u, v) if color[u] == 0 else (v, u)
            self.pos[a * _SH + b] = len(self.E)
            self.E.append((a, b))
            self.adj[a].append(b)
            self.adj[b].append(a)

    def switch(self, a1, b1, a2, b2):
        """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Caller ensures validity."""
        i = self.pos.pop(a1 * _SH + b1)
        j = self.pos.pop(a2 * _SH + b2)
        self.E[i] = (a1, b2)
        self.E[j] = (a2, b1)
        self.pos[a1 * _SH + b2] = i
        self.pos[a2 * _SH + b1] = j
        adj = self.adj
        adj[a1][adj[a1].index(b1)] = b2
        adj[b1][adj[b1].index(a1)] = a2
        adj[a2][adj[a2].index(b2)] = b1
        adj[b2][adj[b2].index(a2)] = a1

    def cost(self, D):
        """Return (number of unordered pairs at distance > D, reach bitmasks)."""
        n = self.n
        adj = self.adj
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
        unr = sum(n - r.bit_count() for r in reach) // 2
        return unr, reach

    def edge_list(self):
        return [(a, b) for a, b in self.E]


def _anneal(g, D, rng, deadline, iters, temp0):
    """Repair defects by edge switches targeted at unreached vertices. True if diameter <= D."""
    n = g.n
    full = (1 << n) - 1
    cost, reach = g.cost(D)
    for t in range(iters):
        if cost == 0:
            return True
        if time.monotonic() > deadline:
            break
        temp = temp0 * (1.0 - t / iters) + 0.05
        u = -1
        for _ in range(40):
            c = rng.randrange(n)
            if reach[c] != full:
                u = c
                break
        if u < 0:
            u = rng.randrange(n)
        if not g.adj[u]:
            continue
        w = rng.choice(g.adj[u])
        if g.color[u] == 0:
            a1, b1 = u, w
        else:
            a1, b1 = w, u
        j = rng.randrange(len(g.E))
        a2, b2 = g.E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1 * _SH + b2) in g.pos or (a2 * _SH + b1) in g.pos:
            continue
        g.switch(a1, b1, a2, b2)
        c2, r2 = g.cost(D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
        else:
            g.switch(a1, b2, a2, b1)
    return cost == 0


def _grow(n, edges, color, d, rng):
    """Add two vertices x (side 0), y (side 1) and edge x-y; reattach d-1 removed edges.

    Returns (n+2, new_edges, new_color), or None if d-1 disjoint edges cannot be found.
    """
    order = list(range(len(edges)))
    rng.shuffle(order)
    usedA, usedB = set(), set()
    pairs = []
    for t in order:
        if len(pairs) == d - 1:
            break
        u, v = edges[t]
        a, b = (u, v) if color[u] == 0 else (v, u)
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        pairs.append((t, a, b))
    if len(pairs) < d - 1:
        return None
    chosen = {t for t, _, _ in pairs}
    x, y = n, n + 1
    cand = [e for t, e in enumerate(edges) if t not in chosen]
    for _, a, b in pairs:
        cand.append((x, b))
        cand.append((y, a))
    cand.append((x, y))
    return n + 2, cand, list(color) + [0, 1]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.90 * time_limit, time_limit - 5.0))
    deadline = start + budget
    lift_deadline = start + 0.40 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < lift_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: bi-Cayley lift search over semidirect products.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < lift_deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        grp = _sample_group(target, rng)
        if grp is None:
            continue
        m, k2, r = grp
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, lift_deadline, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Phase 2: grow by vertex pairs and repair with edge-switch annealing.
    color = _two_color(best_n, best[1]) if best_n >= 2 else None
    if color is not None and d >= 3:
        cur_n, cur_edges, cur_color = best_n, list(best[1]), color
        while time.monotonic() < deadline:
            cand = _grow(cur_n, cur_edges, cur_color, d, rng)
            if cand is None:
                break
            n2, e2, c2 = cand
            g = _Graph(n2, e2, c2)
            if _anneal(g, D, rng, deadline, 800, 2.0):
                ce = g.edge_list()
                if lib.is_valid(n2, ce, d, D):
                    best = (n2, ce)
                    best_n = n2
                    cur_n, cur_edges, cur_color = n2, ce, c2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
