"""Deletion-augmented arc extension of PG(2, q) incidence graphs (diameter 3).

Base construction (as in the parent): take the point-line incidence graph of PG(2, q)
(points 0..m-1, lines m..2m-1). For a set S of k point/line indices, add an A-vertex per
P in S joined to the q+1 lines through P, and a B-vertex per j in S joined to the q+1
points on j. An old line L then gains cl(L) = #{P in S : P on L} degree and an old point Q
gains cp(Q) = #{j in S : Q on j}. The graph has max degree d when cl, cp <= s = d-q-1.

New idea (deletion-augmented arcs): allow k > max load-feasible arc size. Choose S by
simulated annealing that minimises the total overload sum max(0, cl-s) + max(0, cp-s).
Then repair every overload by deleting incidences (Q, L) of PG(2, q): each deletion frees
one unit at a point and one unit at a line. Lines in S are preferred, because the B-vertex
of L then covers the pairs of points on L that the deletion breaks. The result is saturated
with spare X-Y edges and checked with lib.is_valid. Any failure just means a different
random attempt is tried. The fallback is the parent's conic / plain incidence graph,
so the program never returns less than the verified baseline.
"""
import math
import random
import time

import lib


def _pg(q):
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _conic(q):
    """Conic (plus nucleus for even q) as an index set; used as a baseline arc."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _counts(S, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return cl, cp


def _apply(P, dlt, s, point_lines, line_points, cl, cp):
    """Add dlt (+1/-1) to the loads caused by index P; return the change in total overload."""
    de = 0
    for L in point_lines[P]:
        o = cl[L]
        nw = o + dlt
        cl[L] = nw
        de += max(0, nw - s) - max(0, o - s)
    for Q in line_points[P]:
        o = cp[Q]
        nw = o + dlt
        cp[Q] = nw
        de += max(0, nw - s) - max(0, o - s)
    return de


def _anneal(m, s, k, point_lines, line_points, rng, iters, deadline):
    """Anneal a k-subset of indices to minimise total overload. Returns (best_cost, best_S)."""
    S = rng.sample(range(m), k)
    inS = [False] * m
    for P in S:
        inS[P] = True
    cl = [0] * m
    cp = [0] * m
    cost = 0
    for P in S:
        cost += _apply(P, 1, s, point_lines, line_points, cl, cp)
    best_cost, best_S = cost, list(S)
    t0, t1 = 1.0, 0.05
    for it in range(iters):
        if cost == 0:
            break
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        T = t0 * (t1 / t0) ** (it / iters)
        i = rng.randrange(k)
        a = S[i]
        b = rng.randrange(m)
        if inS[b]:
            continue
        de = _apply(a, -1, s, point_lines, line_points, cl, cp)
        de += _apply(b, 1, s, point_lines, line_points, cl, cp)
        if de <= 0 or rng.random() < math.exp(-de / T):
            cost += de
            S[i] = b
            inS[a] = False
            inS[b] = True
            if cost < best_cost:
                best_cost, best_S = cost, list(S)
        else:
            _apply(b, -1, s, point_lines, line_points, cl, cp)
            _apply(a, 1, s, point_lines, line_points, cl, cp)
    return best_cost, best_S


def _plan(S, m, point_lines, line_points, s, rng):
    """Choose incidences (Q, L) to delete so that every overloaded point and line gets enough slack.

    Returns a set of deleted (point, line) pairs, or None if the greedy plan gets stuck.
    """
    cl, cp = _counts(S, m, point_lines, line_points)
    rem = [max(0, c - s) for c in cl]      # deletions still needed at each line
    need = [max(0, c - s) for c in cp]     # deletions needed at each point
    inS = [False] * m
    for P in S:
        inS[P] = True
    deleted = set()
    pts = [Q for Q in range(m) if need[Q] > 0]
    rng.shuffle(pts)
    for Q in pts:
        for _ in range(need[Q]):
            cand = [L for L in point_lines[Q] if (Q, L) not in deleted]
            if not cand:
                return None
            rng.shuffle(cand)
            # Prefer lines that still need slack, then lines in S (their B-vertex repairs pairs).
            L = max(cand, key=lambda x: (rem[x] > 0, inS[x], rem[x]))
            deleted.add((Q, L))
            if rem[L] > 0:
                rem[L] -= 1
    for L in range(m):
        while rem[L] > 0:
            cand = [Q for Q in line_points[L] if (Q, L) not in deleted]
            if not cand:
                return None
            Q = rng.choice(cand)
            deleted.add((Q, L))
            rem[L] -= 1
    return deleted


def _assemble(m, edges, point_lines, line_points, S, deleted):
    k = len(S)
    E = [(u, v) for u, v in edges if (u, v - m) not in deleted]
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return 2 * m + 2 * k, E


def _saturate(n, E, m, k, d, rng):
    """Add X-Y edges between vertices with spare degree (keeps bipartite, never lengthens paths)."""
    S_set = {(min(u, v), max(u, v)) for u, v in E}
    deg = [0] * n
    for u, v in S_set:
        deg[u] += 1
        deg[v] += 1
    X = [v for v in range(n) if v < m or 2 * m <= v < 2 * m + k]
    Y = [v for v in range(n) if m <= v < 2 * m or v >= 2 * m + k]
    pairs = [(x, y) for x in X if deg[x] < d for y in Y if deg[y] < d]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d:
            continue
        key = (min(x, y), max(x, y))
        if key in S_set:
            continue
        S_set.add(key)
        deg[x] += 1
        deg[y] += 1
    return n, sorted(S_set)


def _search_q(d, D, q, deadline, rng):
    """Best verified graph from PG(2, q) with the arc/deletion construction, or None."""
    s = d - q - 1
    m, edges, pl, lp = _pg(q)
    best = [None, 0]

    def consider(S, deleted):
        n, E = _assemble(m, edges, pl, lp, S, deleted)
        n, E = _saturate(n, E, m, len(S), d, rng)
        if n > best[1] and lib.is_valid(n, E, d, D):
            best[0] = (n, E)
            best[1] = n

    consider([], set())                       # plain incidence graph, order 2(q^2+q+1)
    if s >= 2:
        consider(_conic(q), set())            # parent's record family baseline
        targets = list(range(q + 1, q + 6))   # sizes beyond the load-feasible arc bound
        for idx, k in enumerate(targets):
            now = time.monotonic()
            if now >= deadline:
                break
            kd = now + (deadline - now) / (len(targets) - idx)
            while time.monotonic() < kd:
                cost, S = _anneal(m, s, k, pl, lp, rng, 4000, kd)
                if cost == 0:
                    consider(S, set())
                else:
                    dl = _plan(S, m, pl, lp, s, rng)
                    if dl is not None:
                        consider(S, dl)
    return best[0]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.7 * time_limit)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: diameter 2, valid for D >= 2
    if D == 2:
        return fallback

    rng = random.Random(seed * 1000003 + d * 131 + D)
    qs = [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)]
    best = fallback
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now >= deadline:
            break
        frac = 0.8 if idx == 0 else 0.5
        qd = now + frac * (deadline - now)
        res = _search_q(d, D, q, qd, rng)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
