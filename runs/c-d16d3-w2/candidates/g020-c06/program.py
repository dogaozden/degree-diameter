"""Arc-extended PG(2,q) start, then annealed vertex growth.

Stage 1 builds the arc-extended projective-plane graphs (the parent's record family).
Stage 2 is the new search: starting from the best of those, repeatedly append one
vertex on a chosen side, attached greedily to cover the same-side vertices, then
anneal the whole bipartite graph (edge additions and endpoint rewires) to drive the
number of pairs at distance > D to zero. Every accepted graph is checked with
lib.is_valid. Growth works for any D >= 3; K_{d,d} is the always-valid fallback.
"""
import math
import random
import time

import lib


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
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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


def _conic(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A-vertex per S point (on lines through it) and a new B-vertex per S line."""
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


def _arc_candidates(d, deadline, rng):
    """(n, edges) for each prime power q with q + 1 <= d, using spare degree s = d - q - 1."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        S = []
        if s >= 1:
            S = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic(q, index, lib.GF(q))
            if len(cs) > len(S) and _loads_ok(cs, s, m, point_lines, line_points):
                S = cs
        if not _loads_ok(S, s, m, point_lines, line_points):
            S = []
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


def _bipartition(n, adj):
    """2-colouring of a bipartite graph given by adjacency sets."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
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


def _to_edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _add_vertex(n, adj, col, side, d, rng):
    """Append vertex n on `side`, joined greedily to opposite-side vertices that cover the same side.

    Returns False (and leaves the state unchanged) if no opposite-side vertex has spare degree.
    """
    adj.append(set())
    col.append(side)
    cand = [v for v in range(n) if col[v] != side and len(adj[v]) < d]
    if not cand:
        adj.pop()
        col.pop()
        return False
    uncovered = {v for v in range(n) if col[v] == side}
    chosen = []
    cs = set()
    while uncovered and len(chosen) < d:
        best, bg = None, 0
        for v in cand:
            if v in cs:
                continue
            g = 0
            for u in adj[v]:
                if u in uncovered:
                    g += 1
            if g > bg:
                best, bg = v, g
        if best is None:
            break
        chosen.append(best)
        cs.add(best)
        uncovered -= adj[best]
    rest = [v for v in cand if v not in cs]
    rng.shuffle(rest)
    for v in rest:
        if len(chosen) >= d:
            break
        chosen.append(v)
        cs.add(v)
    new = len(adj) - 1
    for v in chosen:
        adj[v].add(new)
        adj[new].add(v)
    return True


def _anneal(n, adj, col, d, D, deadline, rng, max_iters):
    """Metropolis search on edge additions and endpoint rewires until no pair is farther than D apart."""
    cost = _bad_pairs(n, adj, D)
    T = 1.0
    for _ in range(max_iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.1, T * 0.997)
        if rng.random() < 0.3:
            a = rng.randrange(n)
            c = rng.randrange(n)
            if a == c or col[a] == col[c] or c in adj[a] or len(adj[a]) >= d or len(adj[c]) >= d:
                continue
            adj[a].add(c)
            adj[c].add(a)
            new = _bad_pairs(n, adj, D)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                adj[a].discard(c)
                adj[c].discard(a)
        else:
            a = rng.randrange(n)
            if not adj[a]:
                continue
            b = rng.choice(sorted(adj[a]))
            c = rng.randrange(n)
            if c == b or col[c] != col[b] or c in adj[a] or len(adj[c]) >= d:
                continue
            adj[a].discard(b)
            adj[b].discard(a)
            adj[a].add(c)
            adj[c].add(a)
            new = _bad_pairs(n, adj, D)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                adj[a].discard(c)
                adj[c].discard(a)
                adj[a].add(b)
                adj[b].add(a)
    return cost == 0


def _grow(n, edges, d, D, deadline, rng):
    """Repeatedly add one vertex and anneal to repair distances; keep only lib.is_valid graphs."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _bipartition(n, adj)
    best = (n, list(edges))
    cur_n = n
    while time.monotonic() < deadline:
        t_adj = [set(s) for s in adj]
        t_col = list(col)
        if not _add_vertex(cur_n, t_adj, t_col, rng.randrange(2), d, rng):
            continue
        nt = cur_n + 1
        if _anneal(nt, t_adj, t_col, d, D, deadline, rng, 1000):
            E = _to_edges(nt, t_adj)
            if lib.is_valid(nt, E, d, D):
                adj, col, cur_n = t_adj, t_col, nt
                best = (nt, E)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Always-valid fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        try:
            cands = _arc_candidates(d, start + 0.25 * time_limit,
                                    random.Random(seed * 7919 + d))
            for n_c, e_c in sorted(cands, key=lambda t: -t[0]):
                if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                    best = (n_c, e_c)
                    break
        except Exception:
            pass

        try:
            if best[0] > 2:
                n_g, e_g = _grow(best[0], best[1], d, D, deadline, rng)
                if n_g > best[0] and lib.is_valid(n_g, e_g, d, D):
                    best = (n_g, e_g)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
