"""Arc-extended projective plane base plus annealed vertex insertion (diameter-3 pair-covering repair).

New in this version: a vertex-insertion step that adds a vertex on one side,
joins it to d opposite-side vertices chosen greedily to cover the other side's
neighbourhoods, then repairs the diameter violations by simulated annealing over
degree-preserving 2-opt swaps, endpoint rewires and additions between deficient
vertices. Every accepted state is re-checked with lib.is_valid, and the best valid
graph is always returned.
"""
import math
import random
import time

import lib

_ITERS = 1500


# ----------------------------------------------------------------- base graph

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines of S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, S):
    """PG incidence plus a new A vertex per point of S and a new B vertex per line of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        line_points[v - m].append(u)
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_base(d, deadline, rng):
    """Best arc-extended projective plane graph over prime powers q with q + 1 <= d."""
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index = _pg_data(q)
        options = []
        if s >= 1:
            options.append(_greedy_arc(m, s, pl, lp, rng, 30, deadline))
        if s >= 2:
            options.append(_conic_set(q, index, lib.GF(q)))
        options = [S for S in options if S and _loads_ok(S, s, m, pl, lp)]
        if options:
            S = max(options, key=len)
            n, E = _arc_graph(m, edges, pl, S)
        else:
            n, E = 2 * m, list(edges)
        if best is None or n > best[0]:
            best = (n, E)
    return best


def _bipartition(n, adj):
    """Two-colouring by BFS; unreachable vertices default to colour 0."""
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
    return [c if c >= 0 else 0 for c in color]


# ------------------------------------------------------------- graph state

class _Graph:
    """Mutable bipartite graph: side[v] in {0,1}; every edge joins side 0 to side 1."""

    def __init__(self, n, side, edges, d):
        self.n = n
        self.side = list(side)
        self.d = d
        self.adj = [set() for _ in range(n)]
        for u, v in edges:
            self.adj[u].add(v)
            self.adj[v].add(u)

    def edges(self):
        return [(u, v) for u in range(self.n) if self.side[u] == 0 for v in self.adj[u]]

    def snapshot(self):
        return (self.n, list(self.side), [set(s) for s in self.adj])

    def restore(self, snap):
        n, side, adj = snap
        self.n = n
        self.side = list(side)
        self.adj = [set(s) for s in adj]


def _cost(g, D):
    """Number of unordered vertex pairs at distance more than D (0 means valid)."""
    n, adj = g.n, g.adj
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _insert(g, c, rng):
    """Add a vertex on side c joined to <= d side-(1-c) vertices whose neighbourhoods cover side c."""
    other = 1 - c
    uncovered = {v for v in range(g.n) if g.side[v] == c}
    cands = [s for s in range(g.n) if g.side[s] == other]
    chosen = set()
    for _ in range(g.d):
        best_s, best_val = None, -1.0
        for s in cands:
            if s in chosen:
                continue
            val = sum(1 for t in g.adj[s] if t in uncovered) + 0.5 * rng.random()
            if val > best_val:
                best_s, best_val = s, val
        if best_s is None:
            break
        chosen.add(best_s)
        uncovered.difference_update(g.adj[best_s])
    v = g.n
    g.n += 1
    g.side.append(c)
    g.adj.append(set())
    for s in chosen:
        if len(g.adj[s]) >= g.d:
            t = rng.choice(sorted(g.adj[s]))
            g.adj[s].discard(t)
            g.adj[t].discard(s)
        g.adj[s].add(v)
        g.adj[v].add(s)


def _saturate(g, rng):
    """Add edges between deficient opposite-side vertices (never increases distances)."""
    d = g.d
    defs0 = [v for v in range(g.n) if g.side[v] == 0 and len(g.adj[v]) < d]
    defs1 = [v for v in range(g.n) if g.side[v] == 1 and len(g.adj[v]) < d]
    pairs = [(a, b) for a in defs0 for b in defs1 if b not in g.adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(g.adj[a]) < d and len(g.adj[b]) < d and b not in g.adj[a]:
            g.adj[a].add(b)
            g.adj[b].add(a)


def _random_move(g, rng):
    """Return a list of ('rm'|'add', u, v) ops keeping all degrees <= d, or None."""
    n, side, adj, d = g.n, g.side, g.adj, g.d
    r = rng.random()
    if r < 0.3:
        defs0 = [v for v in range(n) if side[v] == 0 and len(adj[v]) < d]
        defs1 = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
        if not defs0 or not defs1:
            return None
        for _ in range(20):
            a = rng.choice(defs0)
            b = rng.choice(defs1)
            if b not in adj[a]:
                return [("add", a, b)]
        return None
    x = rng.randrange(n)
    if not adj[x]:
        return None
    y = rng.choice(sorted(adj[x]))
    a, b = (x, y) if side[x] == 0 else (y, x)
    if r < 0.7:
        x2 = rng.randrange(n)
        if not adj[x2]:
            return None
        y2 = rng.choice(sorted(adj[x2]))
        a2, b2 = (x2, y2) if side[x2] == 0 else (y2, x2)
        if a == a2 or b == b2 or b2 in adj[a] or b in adj[a2]:
            return None
        return [("rm", a, b), ("rm", a2, b2), ("add", a, b2), ("add", a2, b)]
    defs1 = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
    if not defs1:
        return None
    yb = rng.choice(defs1)
    if yb == b or yb in adj[a]:
        return None
    return [("rm", a, b), ("add", a, yb)]


def _apply(g, ops):
    for kind, u, v in ops:
        if kind == "rm":
            g.adj[u].discard(v)
            g.adj[v].discard(u)
        else:
            g.adj[u].add(v)
            g.adj[v].add(u)


def _undo(g, ops):
    for kind, u, v in reversed(ops):
        if kind == "rm":
            g.adj[u].add(v)
            g.adj[v].add(u)
        else:
            g.adj[u].discard(v)
            g.adj[v].discard(u)


def _anneal(g, D, iters, deadline, rng):
    """Metropolis search over degree-preserving moves; returns the final cost (0 = valid)."""
    cur = _cost(g, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = 2.0 * (0.02 ** (it / iters))
        ops = _random_move(g, rng)
        if ops is None:
            continue
        _apply(g, ops)
        new = _cost(g, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
        else:
            _undo(g, ops)
    return cur


def _moore(d, D):
    return 2 * sum((d - 1) ** i for i in range(D))


# -------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D == 2 or d < 3:
        return fallback

    base = _arc_base(d, start + 0.2 * time_limit, rng)
    if base is None or not lib.is_valid(base[0], base[1], d, D):
        return fallback
    n, edges = base
    best = (n, edges)
    if n >= _moore(d, D):
        return best

    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    g = _Graph(n, _bipartition(n, adj), edges, d)
    _saturate(g, rng)
    sat = g.edges()
    if lib.is_valid(g.n, sat, d, D):
        best = (g.n, sat)

    while time.monotonic() < deadline:
        snap = g.snapshot()
        _insert(g, rng.randrange(2), rng)
        cur = _anneal(g, D, _ITERS, deadline, rng)
        if cur == 0:
            _saturate(g, rng)
            e = g.edges()
            if lib.is_valid(g.n, e, d, D):
                best = (g.n, e)
                continue  # keep growing from the repaired state
        g.restore(snap)

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
