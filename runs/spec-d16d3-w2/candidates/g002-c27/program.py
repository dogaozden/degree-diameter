"""Diameter-3 bipartite search: algebraic arc extension plus annealed extra vertices.

Baseline: incidence graph of PG(2, q) with extra A/B vertices placed on an arc
(conic/hyperoval) S, which gives 2(q^2+q+1) + 2|S| vertices. For d = 16 this is
q = 13 and |S| = 14, i.e. 394 vertices.

Bold step: add one extra X/Y vertex pair and anneal the edge set (endpoint
rewires and 2-switches) to minimise the number of ordered pairs at distance
greater than D. Degree <= d and bipartiteness are preserved by every move.
Any result is accepted only if lib.is_valid confirms it; otherwise the
algebraic baseline or the K_{d,d} fallback is returned.
"""
import math
import random
import time

import lib


def _bad(n, adj, D):
    """Ordered pairs at distance > D (zero iff connected with diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(n - r.bit_count() for r in reach)


def _loads_ok(S, s, m, lop, pol):
    """Every line holds <= s points of S and every point lies on <= s lines of S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in lop[P]:
            cl[L] += 1
        for Q in pol[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _arc_candidate(q, d):
    """PG(2,q) incidence plus new A/B vertices on an arc S. Returns (n, edges, side) or None."""
    s = d - q - 1
    if s < 0:
        return None
    n2, inc = lib.projective_plane_incidence(q)
    m = n2 // 2
    lop = [[] for _ in range(m)]   # lines through point P
    pol = [[] for _ in range(m)]   # points on line L
    for u, v in inc:
        lop[u].append(v - m)
        pol[v - m].append(u)
    S = []
    if s >= 2:
        index = {p: i for i, p in enumerate(lib.projective_points(q))}
        F = lib.GF(q)
        cs = [index[(1, t, F.mul(t, t))] for t in range(q)]
        cs.append(index[(0, 0, 1)])
        if q % 2 == 0:
            cs.append(index[(0, 1, 0)])
        if _loads_ok(cs, s, m, lop, pol):
            S = cs
    k = len(S)
    E = list(inc)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in lop[P]:
            E.append((x, m + L))
    for t, P in enumerate(S):
        y = 2 * m + k + t
        for Q in pol[P]:
            E.append((Q, y))
    n = 2 * m + 2 * k
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _best_arc(d):
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        cand = _arc_candidate(q, d)
        if cand is not None and (best is None or cand[0] > best[0]):
            best = cand
    return best


def _search(n, E, side, d, D, rng, deadline, e):
    """Anneal a graph with e extra X/Y vertex pairs to diameter <= D. Returns (N, edges) or None."""
    N = n + 2 * e
    sd = list(side) + [0] * e + [1] * e
    Xs = [v for v in range(N) if sd[v] == 0]
    Ys = [v for v in range(N) if sd[v] == 1]
    edges = [[x, y] for x, y in E]
    adj = [set() for _ in range(N)]
    for x, y in edges:
        adj[x].add(y)
        adj[y].add(x)
    if any(len(a) > d for a in adj):
        return None

    def set_edge(i, nx, ny):
        ox, oy = edges[i]
        adj[ox].discard(oy)
        adj[oy].discard(ox)
        adj[nx].add(ny)
        adj[ny].add(nx)
        edges[i] = [nx, ny]

    cur = _bad(N, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 1.5, 0.05
    ne = len(edges)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** ((now - t0) / span)
        r = rng.random()
        if r < 0.8:
            # Move one endpoint of a random edge to another vertex on the same side.
            i = rng.randrange(ne)
            ox, oy = edges[i]
            if r < 0.4:
                nx, ny = ox, Ys[rng.randrange(len(Ys))]
            else:
                nx, ny = Xs[rng.randrange(len(Xs))], oy
            if (nx, ny) == (ox, oy):
                continue
            if ny in adj[nx]:
                continue
            if nx != ox and len(adj[nx]) >= d:
                continue
            if ny != oy and len(adj[ny]) >= d:
                continue
            set_edge(i, nx, ny)
            new = _bad(N, adj, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                set_edge(i, ox, oy)
        else:
            # 2-switch: degree-preserving exchange of two edges.
            i = rng.randrange(ne)
            j = rng.randrange(ne)
            x1, y1 = edges[i]
            x2, y2 = edges[j]
            if i == j or x1 == x2 or y1 == y2 or y2 in adj[x1] or y1 in adj[x2]:
                continue
            set_edge(i, x1, y2)
            set_edge(j, x2, y1)
            new = _bad(N, adj, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                set_edge(j, x2, y2)
                set_edge(i, x1, y1)
    if cur != 0:
        return None
    return N, [(x, y) for x, y in edges]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback

    if D >= 3:
        cand = _best_arc(d)
        if cand is not None:
            n, E, side = cand
            if n > best[0] and lib.is_valid(n, E, d, D):
                best = (n, E)
            # Bold step: spend the remaining budget on annealing extra vertices.
            if D == 3 and n + 2 <= lib.moore_bound(d, D):
                rng = random.Random(seed * 1000003 + d)
                res = _search(n, E, side, d, D, rng, deadline, 1)
                if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                    best = res

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
