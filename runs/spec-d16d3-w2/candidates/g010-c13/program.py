import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base family: PG(2, q) incidence, extended by a conic-based arc (diameter 3).
#
# Let q be the largest prime power with q + 1 <= d, and s = d - q - 1 the spare
# degree. If s >= 2, pick the conic (plus nucleus when q is even) S. Add one
# A-vertex per point of S (joined to the lines through it) and one B-vertex per
# line of S (joined to the points on it). The load checks keep every degree <= d.
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Return (n, edges) for the PG(2,q) based graph with a conic arc extension, or None."""
    q = next((c for c in range(d - 1, 1, -1) if lib.is_prime_power(c)), None)
    if q is None:
        return None
    s = d - q - 1
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    if s < 2:
        return n2, list(edges)

    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)

    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])

    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    if max(cl) > s or max(cp) > s:
        return n2, list(edges)

    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        for L in point_lines[P]:
            E.append((2 * m + t, m + L))
    for t, j in enumerate(S):
        for Q in line_points[j]:
            E.append((Q, 2 * m + k + t))
    return n, E


# ----------------------------------------------------------------------------
# Adjacency-set graph utilities.
# ----------------------------------------------------------------------------

def _from_edges(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _edges_of(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _colors(n, adj):
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


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D, via bitset balls."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _saturate(adj, color, d, rng):
    """Greedily add random edges between deficient opposite-colour vertices (never breaks diameter)."""
    n = len(adj)
    c0 = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    c1 = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in c0 for b in c1 if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d:
            adj[a].add(b)
            adj[b].add(a)


# ----------------------------------------------------------------------------
# Growth by vertex insertion with simulated-annealing repair.
#
# A new vertex z of colour c is joined to up to d opposite-colour vertices.
# Full neighbours give up one random edge so degrees stay <= d. Annealing then
# rewires single edges until every pair is within distance D again. Rewiring
# keeps the graph bipartite and degrees bounded.
# ----------------------------------------------------------------------------

def _add_vertex(adj, color, c, d, rng):
    z = len(adj)
    adj.append(set())
    color.append(c)
    opp = [v for v in range(z) if color[v] != c]
    k = min(d, len(opp))
    for b in rng.sample(opp, k):
        if len(adj[b]) >= d:
            x = rng.choice(list(adj[b]))
            adj[b].discard(x)
            adj[x].discard(b)
        adj[z].add(b)
        adj[b].add(z)
    return z


def _propose(adj, c0, c1, d, rng):
    """Propose removing edge (a,b) and adding (a2,b2) with opposite colours and spare degree."""
    a = rng.choice(c0)
    if not adj[a]:
        return None
    b = rng.choice(list(adj[a]))
    if rng.random() < 0.5:
        for _ in range(20):
            b2 = rng.choice(c1)
            if b2 != b and b2 not in adj[a] and len(adj[b2]) < d:
                return (a, b, a, b2)
        return None
    for _ in range(20):
        a2 = rng.choice(c0)
        if a2 != a and a2 not in adj[b] and len(adj[a2]) < d:
            return (a, b, a2, b)
    return None


def _apply(adj, mv):
    a, b, a2, b2 = mv
    adj[a].discard(b)
    adj[b].discard(a)
    adj[a2].add(b2)
    adj[b2].add(a2)


def _undo(adj, mv):
    a, b, a2, b2 = mv
    adj[a2].discard(b2)
    adj[b2].discard(a2)
    adj[a].add(b)
    adj[b].add(a)


def _anneal(adj, color, d, D, rng, deadline):
    """Anneal single-edge rewires until the graph has diameter <= D. Returns True on success."""
    n = len(adj)
    c0 = [v for v in range(n) if color[v] == 0]
    c1 = [v for v in range(n) if color[v] == 1]
    cost = _bad_pairs(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 1.5, 0.05
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        mv = _propose(adj, c0, c1, d, rng)
        if mv is None:
            continue
        _apply(adj, mv)
        new = _bad_pairs(n, adj, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
        else:
            _undo(adj, mv)
    return cost == 0


def _grow(adj, color, d, D, deadline, rng, offer):
    """Repeatedly insert one vertex and repair. Stop after two consecutive failures."""
    fails = 0
    while time.monotonic() < deadline and fails < 2:
        now = time.monotonic()
        attempt_deadline = min(deadline, now + max(0.5, 0.5 * (deadline - now)))
        c = rng.randrange(2)
        snap_adj = [set(s) for s in adj]
        snap_col = list(color)
        _add_vertex(adj, color, c, d, rng)
        if _anneal(adj, color, d, D, rng, attempt_deadline):
            offer(len(adj), _edges_of(adj))
            fails = 0
        else:
            adj[:] = snap_adj
            color[:] = snap_col
            fails += 1


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    best = lib.haar_graph(d, range(d))

    def offer(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if D >= 3:
        pg = _pg_base(d)
        if pg is not None:
            offer(pg[0], pg[1])
            adj = _from_edges(pg[0], pg[1])
            color = _colors(pg[0], adj)
            _saturate(adj, color, d, rng)
            offer(len(adj), _edges_of(adj))
            _grow(adj, color, d, D, deadline, rng, offer)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
