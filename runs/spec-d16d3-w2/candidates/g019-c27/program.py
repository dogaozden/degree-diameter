import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so with degree cap d it has spare capacity s = d - q - 1. Choose a point set
# S (an arc-like set) so that every line holds <= s points of S and every point
# lies on <= s lines indexed by S. Add a new A-vertex per point of S (joined to
# the q+1 lines through it) and a new B-vertex per element of S (joined to the
# q+1 points on that line).
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
    """Old PG incidence plus a new A-vertex and a new B-vertex per element of S."""
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


def _saturate(n, edges, m, k, d, rng):
    """Add every missing X-Y edge while both endpoints have spare degree <= d.

    X side: old points 0..m-1 and new A-vertices 2m..2m+k-1.
    Y side: old lines m..2m-1 and new B-vertices 2m+k..2m+2k-1.
    Adding X-Y edges keeps the graph bipartite and never increases a distance.
    """
    E = set()
    for u, v in edges:
        E.add((u, v) if u < v else (v, u))
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    X = [v for v in range(n) if v < m or 2 * m <= v < 2 * m + k]
    Y = [v for v in range(n) if m <= v < 2 * m or v >= 2 * m + k]
    spare_x = [v for v in X if deg[v] < d]
    spare_y = [v for v in Y if deg[v] < d]
    pairs = [(x, y) for x in spare_x for y in spare_y]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d:
            continue
        key = (x, y) if x < y else (y, x)
        if key in E:
            continue
        E.add(key)
        deg[x] += 1
        deg[y] += 1
    return n, sorted(E)


def _arc_extensions(d, deadline, rng):
    """Return (n, edges, m, k) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, S)
        k = len(S)
        n_c, e_c = _saturate(n_c, e_c, m, k, d, rng)
        out.append((n_c, e_c, m, k))
    return out


# ----------------------------------------------------------------------------
# New helper: incremental diameter-checked vertex augmentation.
#
# A new vertex w on side s is joined to a set T of opposite-side vertices that
# have spare degree. For diameter 3 in a bipartite graph, w must reach every
# same-side vertex within distance 2, so T must cover all side-s vertices by
# neighbourhoods. T is chosen greedily (maximum new coverage). The candidate is
# accepted only if a bitset reachability check confirms the diameter bound on
# the whole graph, so the output stays valid by construction.
# ----------------------------------------------------------------------------


def _sides(n, m, k):
    """Side labels for the arc construction: 0 for X (points, A-vertices), 1 for Y (lines, B-vertices)."""
    return [1 if (m <= v < 2 * m or v >= 2 * m + k) else 0 for v in range(n)]


def _reach_ok(n, adj, D):
    """True if every pair of vertices is within distance D, using bitmask BFS."""
    full = (1 << n) - 1
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return all(r == full for r in reach)


def _augment(n, edges, side, d, D, deadline, rng):
    """Greedily try to add new vertices with diameter-checked acceptance; return (n, edges)."""
    N = n
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    side = list(side)
    while time_left(deadline):
        s = rng.randrange(2)
        opp = 1 - s
        spare = [v for v in range(N) if side[v] == opp and len(adj[v]) < d]
        if not spare:
            break
        uncovered = {v for v in range(N) if side[v] == s}
        rng.shuffle(spare)
        pool = spare
        chosen = []
        while uncovered and len(chosen) < d and pool:
            best_gain, best_y = 0, None
            for y in pool:
                g = 0
                for u in adj[y]:
                    if u in uncovered:
                        g += 1
                if g > best_gain:
                    best_gain, best_y = g, y
            if best_y is None:
                break
            chosen.append(best_y)
            pool.remove(best_y)
            uncovered.difference_update(adj[best_y])
        if uncovered or not chosen:
            continue
        w = N
        side.append(s)
        adj.append(list(chosen))
        for y in chosen:
            adj[y].append(w)
        N += 1
        if not _reach_ok(N, adj, D):
            N -= 1
            adj.pop()
            side.pop()
            for y in chosen:
                adj[y].pop()
    out = [(u, v) for u in range(N) for v in adj[u] if u < v]
    return N, out


def time_left(deadline):
    """True while the monotonic clock is before the deadline."""
    return time.monotonic() < deadline


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(0.5, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for all D >= 2.
    best = lib.haar_graph(d, range(d))
    best_info = None

    if D >= 3:
        cands = _arc_extensions(d, start + 0.25 * total, rng)
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c, m, k in cands:
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)
                best_info = (m, k)
                break

    if best_info is not None and time_left(deadline):
        m, k = best_info
        side = _sides(best[0], m, k)
        n2, e2 = _augment(best[0], best[1], side, d, D, deadline, rng)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
