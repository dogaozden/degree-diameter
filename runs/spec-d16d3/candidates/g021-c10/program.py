import math
import random
import time

import lib

# Strategy:
#   1. Build projective-plane-based diameter-3 bases (PG(2,q) plus arc extensions).
#      The conic arc on PG(2,13) reproduces the parent's 394.
#   2. For D == 3, ratchet upward: add one A and one B vertex, greedily fill their
#      spare degree, then anneal over edge add / remove / degree-preserving swap
#      moves to minimise the number of vertex pairs at distance > 3. Accept only
#      states that pass lib.is_valid.
#   3. Every returned graph passes lib.is_valid, falling back to K_{d,d}.
# The ratchet is exploratory: it may not beat the record, but it never returns less
# than the verified base.


def _bipartite_moore(d):
    """Moore bound for bipartite graphs with max degree d and diameter 3."""
    return 2 * (1 + (d - 1) + (d - 1) ** 2)


# ----------------------------------------------------------------------------
# Projective plane and arc extensions (diameter 3).
# ----------------------------------------------------------------------------

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
    """Randomised greedy point set with all loads <= s."""
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


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG incidence plus a new A vertex per point of S and a new B vertex per element of S."""
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


def _pg_candidates(d, deadline, rng):
    """Plain PG incidence graphs and arc-extended graphs for prime powers q <= d - 1."""
    out = []
    for q in range(min(d - 1, 31), 1, -1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        m, edges, pl, lp, index, _pts = _pg_data(q)
        out.append((2 * m, edges))
        s = d - q - 1
        if s < 1:
            continue
        cands = [_greedy_arc(m, s, pl, lp, rng, 30, deadline)]
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if S and _loads_ok(S, s, m, pl, lp):
            out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Ratchet with edge-level annealing (D == 3).
# ----------------------------------------------------------------------------

def _to_adj(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _edges_from_adj(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _two_colour(n, adj):
    """Two-colouring of a bipartite graph given by adjacency sets."""
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


def _bad_pairs(n, adj):
    """Number of unordered vertex pairs at distance > 3 (bitmask ball of radius 3)."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        nxt = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt[v] = r
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal(n, adj, col, d, rng, deadline, iters):
    """Annealing over edge add, edge remove and degree-preserving swap moves.

    Edges only join opposite colours, so the graph stays bipartite.
    Returns the final cost; cost 0 means diameter <= 3.
    """
    side = [[v for v in range(n) if col[v] == 0], [v for v in range(n) if col[v] == 1]]
    cost = _bad_pairs(n, adj)
    T0, T1 = 1.5, 0.15
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters - 1))
        r = rng.random()
        if r < 0.4:
            a = rng.choice(side[0])
            b = rng.choice(side[1])
            if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
                adj[a].add(b)
                adj[b].add(a)
                cost = _bad_pairs(n, adj)
        elif r < 0.6:
            a = rng.choice(side[0])
            if not adj[a]:
                continue
            b = rng.choice(tuple(adj[a]))
            adj[a].discard(b)
            adj[b].discard(a)
            c2 = _bad_pairs(n, adj)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                adj[a].add(b)
                adj[b].add(a)
        else:
            a = rng.choice(side[0])
            c = rng.choice(side[0])
            if a == c or not adj[a] or not adj[c]:
                continue
            b = rng.choice(tuple(adj[a]))
            e = rng.choice(tuple(adj[c]))
            if e in adj[a] or b in adj[c]:
                continue
            # Replace a-b, c-e by a-e, c-b (degrees unchanged).
            adj[a].discard(b)
            adj[b].discard(a)
            adj[c].discard(e)
            adj[e].discard(c)
            adj[a].add(e)
            adj[e].add(a)
            adj[c].add(b)
            adj[b].add(c)
            c2 = _bad_pairs(n, adj)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                adj[a].discard(e)
                adj[e].discard(a)
                adj[c].discard(b)
                adj[b].discard(c)
                adj[a].add(b)
                adj[b].add(a)
                adj[c].add(e)
                adj[e].add(c)
    return cost


def _ratchet(n, edges, d, deadline, rng):
    """Repeatedly add one A and one B vertex, fill greedily, anneal to diameter 3.

    Only states that pass lib.is_valid are kept, so the result is always valid.
    """
    cur_n, cur_e = n, list(edges)
    bound = _bipartite_moore(d)
    while time.monotonic() < deadline:
        if cur_n + 2 > bound:
            break
        adj = _to_adj(cur_n, cur_e)
        col = _two_colour(cur_n, adj)
        adj.append(set())
        adj.append(set())
        col.append(0)
        col.append(1)
        nn = cur_n + 2
        for x in (cur_n, cur_n + 1):
            side = 1 - col[x]
            cands = [v for v in range(nn)
                     if col[v] == side and len(adj[v]) < d and v not in adj[x]]
            rng.shuffle(cands)
            for v in cands:
                if len(adj[x]) >= d:
                    break
                if len(adj[v]) < d and v not in adj[x]:
                    adj[x].add(v)
                    adj[v].add(x)
        sa_deadline = min(deadline, time.monotonic() + 4.0)
        cost = _anneal(nn, adj, col, d, rng, sa_deadline, 500)
        if cost == 0:
            e2 = _edges_from_adj(nn, adj)
            if lib.is_valid(nn, e2, d, 3):
                cur_n, cur_e = nn, e2
                continue
    return cur_n, cur_e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    # Diameter-3 bases (PG incidence graphs, arc extensions).
    for n, e in _pg_candidates(d, start + 0.25 * time_limit, rng):
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Ratchet upward for D == 3.
    if D == 3 and best_n < _bipartite_moore(d):
        n2, e2 = _ratchet(best_n, best_e, d, deadline, rng)
        if n2 > best_n and lib.is_valid(n2, e2, d, D):
            best_n, best_e = n2, e2

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
