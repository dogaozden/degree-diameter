import math
import random
import time
import itertools

import lib


# ----------------------------------------------------------------------------
# Projective-plane base and arc extensions (diameter 3).
#
# From PG(2, q) incidence with spare capacity s = d - q - 1 per vertex, pick a
# point set S with every line holding <= s points of S and every point on <= s
# lines indexed by S. Add an A-vertex per point of S (joined to its q+1 lines)
# and a B-vertex per line of S (joined to its q+1 points). Diameter stays 3.
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
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
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
# Diameter-repair annealing (new in this program).
#
# Start from a valid bipartite graph, add `extra` isolated vertices, and anneal
# over the fixed vertex set with two degree-respecting moves:
#   add     : join two opposite-side vertices with spare degree;
#   rewire  : keep one endpoint of an edge, move the other to a free vertex on
#             the same side as the old endpoint.
# The cost is the number of vertex pairs at distance > D (bitset BFS).
# Each success adds one vertex, so the order grows while the diameter holds.
# ----------------------------------------------------------------------------

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


def _bad_count(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
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


def _pick_free(lst, adj, d, rng, tries=40):
    """Random element of lst with spare degree, or None."""
    for _ in range(tries):
        a = lst[rng.randrange(len(lst))]
        if len(adj[a]) < d:
            return a
    return None


def _repair(n0, edges0, d, D, extra, deadline, rng):
    """Anneal `extra` new vertices into a valid graph; return (n, edges) if diameter holds, else None."""
    n = n0 + extra
    adj = [set() for _ in range(n)]
    for u, v in edges0:
        adj[u].add(v)
        adj[v].add(u)
    base_color = _bipartition(n0, [list(adj[v]) for v in range(n0)])
    color = base_color + [i % 2 for i in range(extra)]
    sides = ([v for v in range(n) if color[v] == 0],
             [v for v in range(n) if color[v] == 1])
    cost = _bad_count(n, adj, D)
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    T0, T1 = 2.0, 0.05

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = T0 * (T1 / T0) ** min(1.0, (now - t_start) / span)

        if rng.random() < 0.35:
            # add move
            a = _pick_free(list(range(n)), adj, d, rng)
            if a is None:
                continue
            b = _pick_free(sides[1 - color[a]], adj, d, rng)
            if b is None or b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            new = _bad_count(n, adj, D)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                adj[a].discard(b)
                adj[b].discard(a)
        else:
            # rewire move: keep a, replace b by a free x on b's side
            a = rng.randrange(n)
            if not adj[a]:
                continue
            b = rng.choice(tuple(adj[a]))
            x = _pick_free(sides[color[b]], adj, d, rng)
            if x is None or x == b or x in adj[a]:
                continue
            adj[a].discard(b)
            adj[b].discard(a)
            adj[a].add(x)
            adj[x].add(a)
            new = _bad_count(n, adj, D)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                adj[a].discard(x)
                adj[x].discard(a)
                adj[a].add(b)
                adj[b].add(a)

    edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, edges


def _repair_loop(best_n, best_e, d, D, seed, deadline, moore):
    """Repeatedly grow the best valid graph by one vertex until time runs out."""
    rng = random.Random(seed + 17)
    while best_n < moore:
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.5:
            break
        seg = min(remaining, max(4.0, remaining / 3))
        res = _repair(best_n, best_e, d, D, 1, now + seg, rng)
        if res is not None:
            n_new, e_new = res
            if lib.is_valid(n_new, e_new, d, D):
                best_n, best_e = n_new, e_new
    return best_n, best_e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        for n_c, e_c in _arc_extensions(d, start + 0.3 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

        moore = lib._moore_bound(d, D)
        if best_n < moore:
            best_n, best_e = _repair_loop(best_n, best_e, d, D, seed, deadline, moore)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
