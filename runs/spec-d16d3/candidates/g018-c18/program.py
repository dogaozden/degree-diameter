import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions (diameter 3): projective plane and arc-extended planes.
#
# Arc extension: for PG(2, q) with spare degree s = d - q - 1, pick S with every
# line meeting S in <= s points. Add an A-vertex per point of S and a B-vertex per
# element of S (as a line). This keeps diameter 3 for any such S.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pg_data(q):
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


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
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
# Bipartition and fast all-pairs-within-D cost (bitsets).
# ----------------------------------------------------------------------------

def _sides(n, edges):
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


def _bad(n, nbr, D):
    """Number of unordered pairs at distance > D (unreachable counts)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# Bold change: degree-preserving simulated annealing repair on a general
# bipartite graph. We add one vertex per side, saturate, then anneal the
# number of pairs at distance > D toward zero using edge swaps (a,b),(c,e)
# -> (a,e),(c,b) and edge additions between deficient opposite-side vertices.
# This explores graphs not of algebraic form.
# ----------------------------------------------------------------------------

def _repair(n, nbr, side, d, D, deadline, rng):
    E = [(u, v) for u in range(n) if side[u] == 0 for v in nbr[u]]
    cost = _bad(n, nbr, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 2.0 * (0.05 ** ((now - t0) / span))
        if len(E) < 2 or rng.random() < 0.1:
            A0 = [u for u in range(n) if side[u] == 0 and len(nbr[u]) < d]
            B1 = [v for v in range(n) if side[v] == 1 and len(nbr[v]) < d]
            if not A0 or not B1:
                continue
            u = rng.choice(A0)
            v = rng.choice(B1)
            if v in nbr[u]:
                continue
            nbr[u].add(v)
            nbr[v].add(u)
            E.append((u, v))
            c2 = _bad(n, nbr, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                nbr[u].discard(v)
                nbr[v].discard(u)
                E.pop()
        else:
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            if i == j:
                continue
            u1, v1 = E[i]
            u2, v2 = E[j]
            if u1 == u2 or v1 == v2 or v2 in nbr[u1] or v1 in nbr[u2]:
                continue
            nbr[u1].discard(v1); nbr[v1].discard(u1)
            nbr[u2].discard(v2); nbr[v2].discard(u2)
            nbr[u1].add(v2); nbr[v2].add(u1)
            nbr[u2].add(v1); nbr[v1].add(u2)
            c2 = _bad(n, nbr, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
                E[i] = (u1, v2)
                E[j] = (u2, v1)
            else:
                nbr[u1].discard(v2); nbr[v2].discard(u1)
                nbr[u2].discard(v1); nbr[v1].discard(u2)
                nbr[u1].add(v1); nbr[v1].add(u1)
                nbr[u2].add(v2); nbr[v2].add(u2)
    return cost == 0


def _grow_repair(n, edges, d, D, deadline, rng):
    """Add one vertex per side, saturate, anneal. Returns (n+2, edges) or None."""
    side = _sides(n, edges)
    N = n + 2
    nbr = [set() for _ in range(N)]
    for u, v in edges:
        nbr[u].add(v)
        nbr[v].add(u)
    side2 = list(side) + [0, 1]
    left = [x for x in range(N) if side2[x] == 0 and len(nbr[x]) < d]
    right = [y for y in range(N) if side2[y] == 1 and len(nbr[y]) < d]
    pairs = [(x, y) for x in left for y in right if y not in nbr[x]]
    rng.shuffle(pairs)
    for x, y in pairs:
        if len(nbr[x]) < d and len(nbr[y]) < d and y not in nbr[x]:
            nbr[x].add(y)
            nbr[y].add(x)
    if _repair(N, nbr, side2, d, D, deadline, rng):
        out = [(u, v) for u in range(N) if side2[u] == 0 for v in nbr[u]]
        return N, out
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    # Bold search: grow the best valid graph by two vertices and anneal-repair.
    bound = lib._moore_bound(d, D)
    cur_n, cur_e = best
    while time.monotonic() < deadline and cur_n < bound:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = now + max(3.0, 0.25 * remaining)
        slice_end = min(slice_end, deadline)
        res = _grow_repair(cur_n, cur_e, d, D, slice_end, rng)
        if res is None:
            continue
        n2, e2 = res
        if lib.is_valid(n2, e2, d, D):
            cur_n, cur_e = n2, e2
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
