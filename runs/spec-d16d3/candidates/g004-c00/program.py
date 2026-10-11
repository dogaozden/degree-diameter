import math
import random
import time

import lib


# Approach for D = 3:
#   1. Baseline: projective plane PG(2, q) incidence, plus an arc extension that
#      uses the spare degree (a conic/hyperoval S, with A and B vertices).
#   2. Growth: add one vertex at a time, fill it greedily, then repair with
#      annealed edge moves. The cost is the number of pairs at distance > D.
#      A candidate is kept only if the cost reaches zero and lib.is_valid passes.
# Every returned graph is checked with lib.is_valid, with a K_{d,d} fallback.
# Other values of D only get the simpler baselines.


def _two_color(n, adj):
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


def _cost(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs count). Zero means valid."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _edges_of(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _spare_on(n, adj, d, rng, want, side, tries=80):
    """Random vertex with spare degree (on side `want` if not None), or None."""
    for _ in range(tries):
        v = rng.randrange(n)
        if len(adj[v]) < d and (want is None or side[v] == want):
            return v
    return None


def _anneal(n, adj, side, d, D, deadline, rng, iters):
    """Annealed repair. Mutates adj in place. Returns the final cost (0 means valid)."""
    cost = _cost(n, adj, D)
    T = 0.5
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.995)
        if rng.random() < 0.4:
            # Add an edge between two spare vertices on opposite sides.
            # Adding edges never increases the cost, so no acceptance test is needed.
            x = _spare_on(n, adj, d, rng, None, side)
            if x is None:
                continue
            y = _spare_on(n, adj, d, rng, 1 - side[x], side)
            if y is None or y in adj[x]:
                continue
            adj[x].add(y)
            adj[y].add(x)
            cost = _cost(n, adj, D)
            continue
        # Rewire: keep edge (a, b) with a on side 0, b on side 1, move one endpoint.
        a = rng.randrange(n)
        if not adj[a]:
            continue
        b = rng.choice(list(adj[a]))
        if side[a] == 1:
            a, b = b, a
        if rng.random() < 0.5:
            nb = _spare_on(n, adj, d, rng, 1, side)
            if nb is None or nb in adj[a]:
                continue
            adj[a].discard(b)
            adj[b].discard(a)
            adj[a].add(nb)
            adj[nb].add(a)
            new = _cost(n, adj, D)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                adj[a].discard(nb)
                adj[nb].discard(a)
                adj[a].add(b)
                adj[b].add(a)
        else:
            na = _spare_on(n, adj, d, rng, 0, side)
            if na is None or na in adj[b]:
                continue
            adj[a].discard(b)
            adj[b].discard(a)
            adj[na].add(b)
            adj[b].add(na)
            new = _cost(n, adj, D)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                adj[na].discard(b)
                adj[b].discard(na)
                adj[a].add(b)
                adj[b].add(a)
    return cost


def _grow(base, d, D, deadline, rng):
    """Repeatedly add one vertex and repair it. Keep only cost-zero, valid results."""
    n, edges = base
    best_adj = [set() for _ in range(n)]
    for u, v in edges:
        best_adj[u].add(v)
        best_adj[v].add(u)
    best_side = _two_color(n, best_adj)
    best_n = n
    moore = 2 * sum((d - 1) ** i for i in range(D))
    while time.monotonic() < deadline and best_n < moore:
        cadj = [set(s) for s in best_adj]
        cside = list(best_side)
        c = rng.randrange(2)
        cadj.append(set())
        cside.append(c)
        opp = [w for w in range(best_n) if cside[w] == 1 - c and len(cadj[w]) < d]
        rng.shuffle(opp)
        v = best_n
        for w in opp[:d]:
            cadj[v].add(w)
            cadj[w].add(v)
        cn = best_n + 1
        cost = _anneal(cn, cadj, cside, d, D, deadline, rng, iters=400)
        if cost == 0:
            E = _edges_of(cn, cadj)
            if lib.is_valid(cn, E, d, D):
                best_n, best_adj, best_side = cn, cadj, cside
    return best_n, _edges_of(best_n, best_adj)


def _pg_candidates(d):
    """Plain PG(2, q) incidence and the arc-extended version, for the largest prime power q with q + 1 <= d."""
    out = []
    q = next((c for c in range(d - 1, 1, -1) if lib.is_prime_power(c)), None)
    if q is None:
        return out
    n2, edges = lib.projective_plane_incidence(q)
    out.append((n2, edges))
    m = n2 // 2
    s = d - q - 1
    if s < 1:
        return out
    if s == 1:
        S = [0]
    else:
        F = lib.GF(q)
        pts = lib.projective_points(q)
        idx = {p: i for i, p in enumerate(pts)}
        # Conic (q+1 points, an arc), plus the nucleus for even q (a hyperoval).
        S = [idx[(1, t, F.mul(t, t))] for t in range(q)] + [idx[(0, 0, 1)]]
        if q % 2 == 0:
            S.append(idx[(0, 1, 0)])
    k = len(S)
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    out.append((2 * m + 2 * k, E))
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 0.5
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    rng = random.Random(seed)

    if D >= 3 and d >= 3:
        for cand in _pg_candidates(d):
            if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                best = cand

    moore = 2 * sum((d - 1) ** i for i in range(D)) if d >= 3 else 0
    if D == 3 and d >= 3 and best[0] < moore and time.monotonic() < deadline:
        n2, e2 = _grow(best, d, D, deadline, rng)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
