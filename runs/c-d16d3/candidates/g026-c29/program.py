import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs: PG(2, q) incidence graphs extended by arcs (diameter 3).
#
# Old vertices have degree q+1, so each has spare capacity s = d - q - 1.
# A point set S with every line holding <= s points of S, and every point on
# <= s lines indexed by S, lets us add one new A-vertex per P in S (joined to the
# lines through P) and one new B-vertex per j in S (joined to the points on j).
# For q = 13, d = 16 the conic gives the known 394-vertex graph.
# ----------------------------------------------------------------------------

def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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


def _arc_base(q, s, rng, deadline):
    """Return (n, edges, color) for the arc-extended PG(2,q) graph with spare s."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    S = []
    if s >= 1:
        cands = []
        if s >= 2:
            F = lib.GF(q)
            index = {p: i for i, p in enumerate(lib.projective_points(q))}
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 30, deadline))
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            S = []
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
    color = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, color


def _best_base(d, rng, deadline, D):
    cands = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 0:
            continue
        if cands and time.monotonic() > deadline:
            break
        cands.append(_arc_base(q, s, rng, deadline))
    cands.sort(key=lambda t: -t[0])
    for n, E, color in cands:
        if lib.is_valid(n, E, d, D):
            return n, E, color
    return None


# ----------------------------------------------------------------------------
# NEW: annealing over graphs with inserted vertices.
#
# State: a bipartite graph (colour classes kept explicit) with max degree d.
# Cost = number of vertex pairs at distance > D. Moves slide an edge endpoint
# or add a spare edge; cost 0 means valid. Whenever the state is valid, a new
# vertex is inserted, greedily covering as many vertices as possible within
# radius D-1 of its neighbours. The annealing then repairs the uncovered pairs
# by rewiring, instead of demanding a perfect cover up front. On stall, the
# last valid snapshot is restored and a different insertion is tried.
# ----------------------------------------------------------------------------

def _balls(n, adj, R):
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _bad(n, adj, D):
    return sum(n - r.bit_count() for r in _balls(n, adj, D)) // 2


def _move(n, adj, color, d, rng):
    spare0 = [x for x in range(n) if color[x] == 0 and len(adj[x]) < d]
    spare1 = [x for x in range(n) if color[x] == 1 and len(adj[x]) < d]
    r = rng.random()
    if r < 0.15:
        if not spare0 or not spare1:
            return None
        for _ in range(10):
            u = rng.choice(spare0)
            v = rng.choice(spare1)
            if v not in adj[u]:
                return [("add", u, v)]
        return None
    cols0 = [x for x in range(n) if color[x] == 0 and adj[x]]
    cols1 = [x for x in range(n) if color[x] == 1 and adj[x]]
    if not cols0 or not cols1:
        return None
    if r < 0.575:
        v = rng.choice(cols1)
        u = rng.choice(list(adj[v]))
        cands = [x for x in spare0 if x not in adj[v]]
        if not cands:
            return None
        u2 = rng.choice(cands)
        return [("rem", u, v), ("add", u2, v)]
    u = rng.choice(cols0)
    v = rng.choice(list(adj[u]))
    cands = [x for x in spare1 if x not in adj[u]]
    if not cands:
        return None
    v2 = rng.choice(cands)
    return [("rem", u, v), ("add", u, v2)]


def _apply(adj, ops):
    for op, u, v in ops:
        if op == "add":
            adj[u].add(v)
            adj[v].add(u)
        else:
            adj[u].discard(v)
            adj[v].discard(u)


def _undo(adj, ops):
    for op, u, v in reversed(ops):
        if op == "add":
            adj[u].discard(v)
            adj[v].discard(u)
        else:
            adj[u].add(v)
            adj[v].add(u)


def _insert(n, adj, color, d, D, rng):
    """Insert one vertex greedily covering within radius D-1 of its neighbours. Returns new n or None."""
    balls = _balls(n, adj, D - 1)
    side = rng.randrange(2)
    cand = [u for u in range(n) if color[u] == 1 - side and len(adj[u]) < d]
    covered = 0
    chosen = []
    while cand and len(chosen) < d:
        gains = [(balls[u] & ~covered).bit_count() for u in cand]
        g = max(gains)
        if g <= 0:
            break
        idx = [i for i, x in enumerate(gains) if x == g]
        u = cand.pop(rng.choice(idx))
        chosen.append(u)
        covered |= balls[u]
    if not chosen:
        return None
    w = n
    adj.append(set())
    color.append(side)
    for u in chosen:
        adj[u].add(w)
        adj[w].add(u)
    return n + 1


def _search(n, edges, color, d, D, rng, deadline):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    cur_n = n
    cost = _bad(cur_n, adj, D)
    best_n, best_edges = -1, None
    snap = None
    T = 0.6
    stall = 0
    while time.monotonic() < deadline:
        if cost == 0:
            if cur_n > best_n:
                best_n = cur_n
                best_edges = [(u, v) for u in range(cur_n) for v in adj[u] if u < v]
            snap = ([set(s) for s in adj], list(color), cur_n)
            res = _insert(cur_n, adj, color, d, D, rng)
            if res is None:
                break
            cur_n = res
            cost = _bad(cur_n, adj, D)
            T = 0.6
            stall = 0
            continue
        ops = _move(cur_n, adj, color, d, rng)
        stall += 1
        if ops is not None:
            _apply(adj, ops)
            c2 = _bad(cur_n, adj, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                _undo(adj, ops)
        T = max(0.05, T * 0.998)
        if stall > 600 and cost > 0 and snap is not None:
            adj_snap, color_snap, n_snap = snap
            adj = [set(s) for s in adj_snap]
            color[:] = color_snap
            cur_n = n_snap
            cost = 0
            stall = 0
            T = 0.6
    return best_n, best_edges


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + max(0.2, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback
    base = _best_base(d, rng, t0 + 0.1 * (end - t0), D)
    if base is not None:
        n, E, color = base
        if n > best[0]:
            best = (n, E)
        res_n, res_E = _search(n, E, list(color), d, D, rng, end)
        if res_E is not None and res_n > best[0] and lib.is_valid(res_n, res_E, d, D):
            best = (res_n, res_E)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
