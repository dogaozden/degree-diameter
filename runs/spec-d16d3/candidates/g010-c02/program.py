import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane bases and arc extensions (diameter-3 starting points).
# ----------------------------------------------------------------------------

def _pg(q):
    """Point/line data of PG(2, q): (m, incidence edges, lines through point, points on line, index)."""
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
    """True if every line gets <= s extra edges and every point gets <= s extra edges from S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of a point set S with all loads <= s; returns the largest found."""
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
    """PG incidence plus one new A-vertex per point of S and one new B-vertex per line of S."""
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
    """(n, edges) candidates, one per prime power q with spare degree s = d - q - 1 >= 1."""
    out = []
    for q in range(min(d - 1, 23), 1, -1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp, index = _pg(q)
        cands = [_greedy_arc(m, s, pl, lp, rng, 40, deadline)]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if S and _loads_ok(S, s, m, pl, lp):
            out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Mutable bipartite state: adjacency sets plus side colours.
# Growth adds one vertex at a time, then repairs with annealed edge moves
# (2-switches and endpoint reassignments, which keep the sides and degree
# bounds intact). A state is accepted only if its diameter is <= D.
# ----------------------------------------------------------------------------

def _from_edges(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
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
    return adj, color


def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _cost(n, adj, D):
    """Ordered pairs at distance > D (zero means diameter <= D)."""
    return sum(n - b.bit_count() for b in _balls(n, adj, D))


def _pick(n, cands, ball, d, rng):
    """Randomized greedy cover of all n existing vertices by at most d candidates."""
    full = (1 << n) - 1
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while pool and len(chosen) < d and covered != full:
        best = None
        bg = 0
        for s in pool:
            g = (ball[s] & ~covered).bit_count()
            if g > bg:
                bg = g
                best = s
        if best is None:
            break
        pool.remove(best)
        chosen.append(best)
        covered |= ball[best]
    return chosen, covered == full


def _fill(n, color, adj, d, rng):
    """Greedily join deficient opposite-side vertices (never increases the cost)."""
    L0 = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    L1 = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    rng.shuffle(L0)
    for a in L0:
        if len(adj[a]) >= d:
            continue
        cand = [b for b in L1 if len(adj[b]) < d and b not in adj[a]]
        rng.shuffle(cand)
        for b in cand:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) < d and b not in adj[a]:
                adj[a].add(b)
                adj[b].add(a)


def _propose(n, color, adj, d, rng):
    """Random degree-preserving 2-switch, or an endpoint reassignment. None if not applicable."""
    a1 = rng.randrange(n)
    if not adj[a1]:
        return None
    b1 = rng.choice(list(adj[a1]))
    a2 = rng.randrange(n)
    if a2 == a1 or color[a2] != color[a1]:
        return None
    if rng.random() < 0.5:
        if not adj[a2]:
            return None
        b2 = rng.choice(list(adj[a2]))
        if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            return None
        return [(a1, b1), (a2, b2)], [(a1, b2), (a2, b1)]
    if len(adj[a2]) >= d or b1 in adj[a2]:
        return None
    return [(a1, b1)], [(a2, b1)]


def _repair(n, color, adj, d, D, rng, deadline, iters):
    """Annealed repair. Returns True iff the state ends with diameter <= D."""
    _fill(n, color, adj, d, rng)
    cost = _cost(n, adj, D)
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 3.0 * (0.05 / 3.0) ** (it / max(1, iters))
        if rng.random() < 0.1:
            _fill(n, color, adj, d, rng)
            cost = _cost(n, adj, D)
            continue
        prop = _propose(n, color, adj, d, rng)
        if prop is None:
            continue
        rem, add = prop
        for u, v in rem:
            adj[u].discard(v)
            adj[v].discard(u)
        for u, v in add:
            adj[u].add(v)
            adj[v].add(u)
        c2 = _cost(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            for u, v in add:
                adj[u].discard(v)
                adj[v].discard(u)
            for u, v in rem:
                adj[u].add(v)
                adj[v].add(u)
    return cost == 0


def _edges_of(n, adj):
    return [(u, w) for u in range(n) for w in adj[u] if u < w]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        for q in range(min(d - 1, 23), 1, -1):
            if lib.is_prime_power(q):
                n0, e0 = lib.projective_plane_incidence(q)
                consider(n0, e0)
        for n1, e1 in _arc_candidates(d, start + 0.2 * time_limit,
                                      random.Random(seed * 7919 + d)):
            consider(n1, e1)

    # Growth by single vertices with annealed repair, starting from the best valid graph.
    cur_adj, cur_color = _from_edges(best_n, best_e)
    cur_n = best_n
    while time.monotonic() < deadline:
        n = cur_n
        adj = [set(s) for s in cur_adj]
        color = list(cur_color)
        c = rng.randrange(2)
        cands = [s for s in range(n) if color[s] == 1 - c and len(adj[s]) < d]
        if not cands:
            c = 1 - c
            cands = [s for s in range(n) if color[s] == 1 - c and len(adj[s]) < d]
            if not cands:
                break
        ball = _balls(n, adj, D - 1)
        chosen, ok = [], False
        for _ in range(5):
            chosen, ok = _pick(n, cands, ball, d, rng)
            if ok:
                break
        v = n
        n += 1
        color.append(c)
        adj.append(set())
        for s in chosen:
            adj[s].add(v)
            adj[v].add(s)
        if ok or _repair(n, color, adj, d, D, rng, deadline, 300):
            cur_n, cur_adj, cur_color = n, adj, color
            consider(n, _edges_of(n, adj))

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
