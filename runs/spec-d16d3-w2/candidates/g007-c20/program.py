import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fallback: arc-extended projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

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


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _attach(m, edges, S, point_lines, line_points):
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
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if time.monotonic() > deadline:
            break
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 0:
            continue
        n2, edges = lib.projective_plane_incidence(q)
        m = n2 // 2
        if s == 0:
            out.append((n2, list(edges)))
            continue
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        point_lines = [[] for _ in range(m)]
        line_points = [[] for _ in range(m)]
        for u, v in edges:
            point_lines[u].append(v - m)
            line_points[v - m].append(u)
        best = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points) and len(cs) > len(best):
                best = cs
        if not best:
            out.append((n2, list(edges)))
            continue
        if not _loads_ok(best, s, m, point_lines, line_points):
            continue
        n, E = _attach(m, edges, best, point_lines, line_points)
        out.append((n, E))
    return out


# ----------------------------------------------------------------------------
# Bold path: start from PG(2,q) with q+1 > d (degree too high), then search
# for the largest induced subgraph with max degree <= d and diameter <= D.
# Removing vertices can only create violations; re-adding a vertex never
# breaks distances between existing vertices, so re-adding only needs a
# local check on the new vertex.
# ----------------------------------------------------------------------------

def _full_reach(n, adj, alive, D):
    act = [v for v in range(n) if alive[v]]
    nbr = [None] * n
    for v in act:
        nbr[v] = [u for u in adj[v] if alive[u]]
    reach = [0] * n
    for v in act:
        reach[v] = 1 << v
    for _ in range(D):
        new = [0] * n
        for v in act:
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return act, nbr, reach


def _repair(n, adj, alive, d, D, rng):
    """Remove vertices until the induced subgraph is valid (degree <= d, diameter <= D)."""
    while True:
        act, nbr, reach = _full_reach(n, adj, alive, D)
        if not act:
            return
        cnt = len(act)
        bad = []
        for v in act:
            miss = cnt - reach[v].bit_count()
            ex = len(nbr[v]) - d
            if miss or ex > 0:
                sc = miss + 200 * max(0, ex)
                bad.append((sc, rng.random(), v))
        if not bad:
            return
        _, _, worst = max(bad)
        alive[worst] = 0


def _covers_all(v, adj, alive, total, D):
    seen = {v}
    frontier = [v]
    for _ in range(D):
        nxt = []
        for x in frontier:
            for y in adj[x]:
                if alive[y] and y not in seen:
                    seen.add(y)
                    nxt.append(y)
        frontier = nxt
        if not frontier:
            break
    return len(seen) == total


def _try_add(v, adj, alive, d, D):
    if alive[v]:
        return False
    nb = [u for u in adj[v] if alive[u]]
    if len(nb) > d:
        return False
    for u in nb:
        if sum(alive[w] for w in adj[u]) >= d:
            return False
    alive[v] = 1
    total = sum(alive)
    if _covers_all(v, adj, alive, total, D):
        return True
    alive[v] = 0
    return False


def _refill(n, adj, alive, d, D, rng):
    dead = [v for v in range(n) if not alive[v]]
    rng.shuffle(dead)
    for v in dead:
        _try_add(v, adj, alive, d, D)


def _bold(q, d, D, deadline, rng):
    n, edges = lib.projective_plane_incidence(q)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    alive = bytearray([1]) * n
    _repair(n, adj, alive, d, D, rng)
    _refill(n, adj, alive, d, D, rng)
    cur = sum(alive)
    best = cur
    best_alive = bytearray(alive)
    while time.monotonic() < deadline:
        saved = bytearray(alive)
        alive_list = [v for v in range(n) if alive[v]]
        if not alive_list:
            break
        k = rng.choice([1, 1, 2, 2, 3, 4, 6])
        for _ in range(k):
            v = rng.choice(alive_list)
            alive[v] = 0
        _repair(n, adj, alive, d, D, rng)
        _refill(n, adj, alive, d, D, rng)
        new = sum(alive)
        if new >= cur or rng.random() < 0.01:
            cur = new
            if cur > best:
                best = cur
                best_alive = bytearray(alive)
        else:
            alive[:] = saved
    return best_alive, adj, n


def _induced_graph(n, adj, alive):
    idx = {}
    for v in range(n):
        if alive[v]:
            idx[v] = len(idx)
    E = []
    for v in idx:
        for u in adj[v]:
            if u in idx and v < u:
                E.append((idx[v], idx[u]))
    return len(idx), E


def _smallest_pg_q(d):
    q = max(d, 2)
    while (not lib.is_prime_power(q)) or q + 1 <= d:
        q += 1
    return q


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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
        arcs = _arc_candidates(d, start + 0.2 * time_limit,
                               random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n, e in arcs:
            consider(n, e)

    # Bold path: deletion-based search on PG(2,q) with q+1 > d.
    if D == 3 and d >= 8:
        q = _smallest_pg_q(d)
        if q <= 25:
            deadline = start + 0.72 * time_limit
            alive, adj, n0 = _bold(q, d, D, deadline,
                                   random.Random(seed * 31 + 7))
            n, e = _induced_graph(n0, adj, alive)
            if n >= 1:
                consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
