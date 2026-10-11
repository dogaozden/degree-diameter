import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Experimental construction for D = 3 (this version).
#
# 1. Safe baseline: incidence graph of PG(2, q) for the largest prime powers
#    q <= d-1, extended with a point set S (conic-like arc) that uses the spare
#    degree d-q-1, then saturated with extra X-Y edges. Every candidate is
#    checked with lib.is_valid before it is kept.
# 2. Bold step: simulated annealing over the bipartite graph itself. Moves are
#    degree-preserving 2-switches and "transfer" moves that shift spare degree.
#    Whenever the current graph has diameter <= D, two new vertices (one per
#    side) are added and the search tries to repair the new pairs. The best
#    verified graph is always returned, so the output never falls below the
#    baseline. This is a heuristic search and is not guaranteed to beat the
#    record.
# ----------------------------------------------------------------------------


def _edges_of(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _bad(n, adj, D):
    """Ordered count of vertex pairs at distance > D (0 means connected with diameter <= D)."""
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
    return sum(n - r.bit_count() for r in reach)


def _pg(q):
    """Points 0..m-1, lines m..2m-1 of PG(2,q), with point->lines and line->points lists."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, point_lines, line_points


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


def _saturate(n, E, side, d, rng):
    """Build adjacency sets from edge list E, then greedily add X-Y edges with spare degree."""
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    X = [v for v in range(n) if side[v] == 0 and len(adj[v]) < d]
    Y = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
    pairs = [(x, y) for x in X for y in Y]
    rng.shuffle(pairs)
    for x, y in pairs:
        if len(adj[x]) < d and len(adj[y]) < d and y not in adj[x]:
            adj[x].add(y)
            adj[y].add(x)
    return adj


def _pg_arc_candidate(q, d, rng, deadline):
    """Arc-extended PG(2,q) incidence graph; returns (n, adj, side)."""
    s = d - q - 1
    m, point_lines, line_points = _pg(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    cands = [[]]
    if s >= 1:
        cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 30, deadline))
    if s >= 2:
        F = lib.GF(q)
        conic = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
        cands.append(conic)
        if q % 2 == 0:
            cands.append(conic + [index[(0, 1, 0)]])
    S = max((c for c in cands if _loads_ok(c, s, m, point_lines, line_points)),
            key=len, default=[])

    k = len(S)
    n = 2 * m + 2 * k
    E = [(u, m + L) for u in range(m) for L in point_lines[u]]
    for t, P in enumerate(S):
        E.extend((2 * m + t, m + L) for L in point_lines[P])
    for t, j in enumerate(S):
        E.extend((Q, 2 * m + k + t) for Q in line_points[j])
    side = [0] * m + [1] * m + [0] * k + [1] * k
    adj = _saturate(n, E, side, d, rng)
    return n, adj, side


def _swap(adj, x1, y1, x2, y2):
    """Remove x1-y1, x2-y2; add x1-y2, x2-y1."""
    adj[x1].discard(y1)
    adj[y1].discard(x1)
    adj[x2].discard(y2)
    adj[y2].discard(x2)
    adj[x1].add(y2)
    adj[y2].add(x1)
    adj[x2].add(y1)
    adj[y1].add(x2)


def _move(adj, u, w, z):
    """Remove z-w; add u-w."""
    adj[z].discard(w)
    adj[w].discard(z)
    adj[u].add(w)
    adj[w].add(u)


def _accept(delta, T, rng):
    return delta <= 0 or rng.random() < math.exp(-delta / T)


def _anneal(n, side, adj, d, D, rng, deadline, best):
    """Annealing with growth. Updates `best` (dict with 'n', 'e') with every verified improvement."""
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    Xall = [v for v in range(n) if side[v] == 0]
    Yall = [v for v in range(n) if side[v] == 1]
    cur = _bad(n, adj, D)

    while time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        T = 0.3 + 2.0 * (1.0 - frac)

        spX = [v for v in Xall if len(adj[v]) < d]
        spY = [v for v in Yall if len(adj[v]) < d]
        added = False
        for x in spX:
            for y in spY:
                if len(adj[x]) >= d:
                    break
                if len(adj[y]) < d and y not in adj[x]:
                    adj[x].add(y)
                    adj[y].add(x)
                    added = True
        if added:
            cur = _bad(n, adj, D)

        if cur == 0:
            e = _edges_of(n, adj)
            if n > best["n"] and lib.is_valid(n, e, d, D):
                best["n"] = n
                best["e"] = e
            # Grow by one vertex per side and try to repair.
            adj.append(set())
            adj.append(set())
            side.extend([0, 1])
            Xall.append(n)
            Yall.append(n + 1)
            n += 2
            cur = _bad(n, adj, D)
            continue

        spare = spX + spY
        if rng.random() < 0.5 or not spare:
            # Degree-preserving 2-switch.
            x1 = rng.choice(Xall)
            x2 = rng.choice(Xall)
            if x1 == x2 or not adj[x1] or not adj[x2]:
                continue
            y1 = rng.choice(tuple(adj[x1]))
            y2 = rng.choice(tuple(adj[x2]))
            if y1 == y2 or y2 in adj[x1] or y1 in adj[x2]:
                continue
            _swap(adj, x1, y1, x2, y2)
            new = _bad(n, adj, D)
            if _accept(new - cur, T, rng):
                cur = new
            else:
                _swap(adj, x1, y2, x2, y1)
        else:
            # Transfer: move a spare slot from u to a neighbour z of a saturated w.
            u = rng.choice(spare)
            w = rng.choice(Yall if side[u] == 0 else Xall)
            if w in adj[u] or len(adj[w]) < d or not adj[w]:
                continue
            z = rng.choice(tuple(adj[w]))
            _move(adj, u, w, z)
            new = _bad(n, adj, D)
            if _accept(new - cur, T, rng):
                cur = new
            else:
                _move(adj, z, w, u)

    if cur == 0 and n > best["n"]:
        e = _edges_of(n, adj)
        if lib.is_valid(n, e, d, D):
            best["n"] = n
            best["e"] = e


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    kdd_e = [(x, d + y) for x in range(d) for y in range(d)]
    best = {"n": 2 * d, "e": kdd_e}
    start = (2 * d,
             [set(range(d, 2 * d)) if v < d else set(range(d)) for v in range(2 * d)],
             [0] * d + [1] * d)

    # Arc-extended projective plane graphs (diameter 3), for the two largest prime powers <= d-1.
    if D >= 3:
        qs = sorted((q for q in range(2, d) if lib.is_prime_power(q)), reverse=True)[:2]
        for q in qs:
            if time.monotonic() > deadline:
                break
            n_c, adj_c, side_c = _pg_arc_candidate(q, d, rng, deadline)
            e_c = _edges_of(n_c, adj_c)
            if n_c > best["n"] and lib.is_valid(n_c, e_c, d, D):
                best = {"n": n_c, "e": e_c}
                start = (n_c, adj_c, side_c)

    # Bold step: annealing with growth, starting from the best verified graph.
    n, side, adj = start[0], list(start[2]), [set(s) for s in start[1]]
    if time.monotonic() < deadline:
        _anneal(n, side, adj, d, D, rng, deadline, best)

    n, e = best["n"], best["e"]
    if not lib.is_valid(n, e, d, D):
        n, e = 2 * d, kdd_e
    return n, e
