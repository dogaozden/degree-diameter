import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: projective plane incidence and arc-extended planes.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Graph helpers.
# ----------------------------------------------------------------------------

def _colors(n, edges):
    """Two-colouring of a bipartite graph (BFS per component)."""
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


def _bad_pairs(n, adj):
    """Number of unordered pairs at distance > 3, using bitset balls of radius 3."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        nxt = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            nxt[v] = x
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# Search: simulated annealing over bipartite graphs with fixed vertex count.
#
# Moves: degree-preserving double edge swaps, adding an edge between two
# deficient vertices on opposite sides, and removing an edge.
# Cost = bad pairs (distance > 3) + deficiency (sum of missing degree).
# Success = zero bad pairs, which yields a valid diameter-3 graph.
# ----------------------------------------------------------------------------

def _sa_extend(n, edges, color, d, deadline, rng, fresh):
    adj = [set() for _ in range(n)]
    E = []
    pos = {}

    def link(u, v):
        if color[u] == 1:
            u, v = v, u
        pos[(u, v)] = len(E)
        E.append((u, v))
        adj[u].add(v)
        adj[v].add(u)

    def unlink(u, v):
        if color[u] == 1:
            u, v = v, u
        i = pos.pop((u, v))
        last = E.pop()
        if i < len(E):
            E[i] = last
            pos[last] = i
        adj[u].discard(v)
        adj[v].discard(u)

    for u, v in edges:
        link(u, v)
    for v in fresh:
        cands = [u for u in range(n)
                 if color[u] != color[v] and len(adj[u]) < d and u not in adj[v]]
        rng.shuffle(cands)
        for u in cands:
            if len(adj[v]) >= d:
                break
            if len(adj[u]) < d and u not in adj[v]:
                link(u, v)

    def bad_cost():
        bad = _bad_pairs(n, adj)
        deff = sum(d - len(a) for a in adj)
        return bad, deff

    bad, deff = bad_cost()
    if bad == 0:
        return list(E)
    cur = bad + deff

    T0, Tend = 1.5, 0.08
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = T0 * (Tend / T0) ** frac

        r = rng.random()
        if r < 0.6:
            if len(E) < 2:
                continue
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            a1, b1 = E[i]
            a2, b2 = E[j]
            if i == j or a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
                continue
            unlink(a1, b1)
            unlink(a2, b2)
            link(a1, b2)
            link(a2, b1)
            kind = 0
        elif r < 0.9:
            defA = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
            defB = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
            if not defA or not defB:
                continue
            a = rng.choice(defA)
            b = rng.choice(defB)
            if b in adj[a]:
                continue
            link(a, b)
            kind = 1
        else:
            if not E:
                continue
            a, b = E[rng.randrange(len(E))]
            unlink(a, b)
            kind = 2

        nb, nd = bad_cost()
        new = nb + nd
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            if nb == 0:
                return list(E)
        else:
            if kind == 0:
                unlink(a1, b2)
                unlink(a2, b1)
                link(a1, b1)
                link(a2, b2)
            elif kind == 1:
                unlink(a, b)
            else:
                link(a, b)
    return None


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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
        for n_c, e_c in _arc_extensions(d, start + 0.3 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    # Bold search for D = 3: grow the best base one vertex at a time,
    # re-wiring with annealing to keep bad pairs at zero.
    if D == 3 and best_n < lib._moore_bound(d, D):
        color = _colors(best_n, best[1])
        while time.monotonic() < deadline:
            n0 = best_n
            ca = sum(1 for c in color if c == 0)
            cb = n0 - ca
            c_new = 0 if ca <= cb else 1
            n_new = n0 + 1
            color2 = color + [c_new]
            res = _sa_extend(n_new, list(best[1]), color2, d, deadline, rng, [n0])
            if res is None:
                break
            before = best_n
            consider(n_new, res)
            if best_n == before:
                break
            color = _colors(best_n, best[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
