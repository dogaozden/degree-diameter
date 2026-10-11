import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction: generalized quadrangle W(q) incidence graph (diameter 4),
# then SHRINK it by simulated annealing over vertex subsets.
#
# Start from W(q) with q+1 >= d (degree q+1 may exceed d). A subset S of
# vertices induces a graph; any vertex with more than d neighbours in S is
# peeled away, so the induced graph always has max degree <= d and is
# bipartite. Annealing maximises |S| - LAM * (bad pairs at distance > D).
# The best subset with zero bad pairs is kept.
#
# This differs from the parent's growth/annealing routes: instead of adding
# vertices to a base, it deletes from a larger, rigid, diameter-4 structure.
# ----------------------------------------------------------------------------

LAM = 0.5


def _gq_w(q):
    """Incidence graph of points and lines of W(q); diameter 4, degree q+1, bipartite."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _peel(alive, adj, d):
    """Remove over-degree alive vertices (in place) until every alive vertex has <= d alive neighbours."""
    n = len(alive)
    deg = [0] * n
    stack = []
    for v in range(n):
        if alive[v]:
            c = 0
            for u in adj[v]:
                if alive[u]:
                    c += 1
            deg[v] = c
            if c > d:
                stack.append(v)
    while stack:
        v = stack.pop()
        if not alive[v] or deg[v] <= d:
            continue
        alive[v] = False
        for u in adj[v]:
            if alive[u]:
                deg[u] -= 1
                if deg[u] > d:
                    stack.append(u)
    return alive


def _bad(alive, adj, D):
    """Number of unordered alive pairs at distance > D in the induced subgraph (bitmask balls)."""
    n = len(alive)
    A = [v for v in range(n) if alive[v]]
    m = len(A)
    if m <= 1:
        return 0
    reach = [0] * n
    for v in A:
        reach[v] = 1 << v
    for _ in range(D):
        new = reach[:]
        for v in A:
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]  # dead vertices have reach 0
            new[v] = r
        reach = new
    total = 0
    for v in A:
        total += m - reach[v].bit_count()
    return total // 2


def _sa(n, adj, d, D, deadline, rng):
    """Simulated annealing over peeled vertex subsets. Returns (best_n, best_alive) with zero bad pairs."""
    alive = _peel([True] * n, adj, d)
    cur_n = sum(alive)
    cur_b = _bad(alive, adj, D)
    cur_f = cur_n - LAM * cur_b
    if cur_b == 0:
        best_n, best_alive = cur_n, alive[:]
    else:
        best_n, best_alive = 0, None

    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 2.0, 0.15
    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        cand = alive[:]
        if rng.random() < 0.5 or cur_n >= n - 1:
            L = [v for v in range(n) if cand[v]]
            if not L:
                break
            cand[rng.choice(L)] = False
        else:
            w = rng.randrange(n)
            while cand[w]:
                w = rng.randrange(n)
            cand[w] = True
            cand = _peel(cand, adj, d)
        n2 = sum(cand)
        b2 = _bad(cand, adj, D)
        f2 = n2 - LAM * b2
        if f2 >= cur_f or rng.random() < math.exp((f2 - cur_f) / T):
            alive, cur_n, cur_b, cur_f = cand, n2, b2, f2
            if b2 == 0 and n2 > best_n:
                best_n, best_alive = n2, alive[:]
    return best_n, best_alive


def _induced(n, adj, alive):
    """Relabel the alive induced subgraph to 0..m-1 and return (m, edges)."""
    idx = {}
    for v in range(n):
        if alive[v]:
            idx[v] = len(idx)
    edges = []
    for v in idx:
        for u in adj[v]:
            if u > v and u in idx:
                edges.append((idx[v], idx[u]))
    return len(idx), edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.8 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        if D == 3:
            # Projective plane incidence graph when d-1 is a prime power (diameter 3).
            for q in range(d - 1, 1, -1):
                if lib.is_prime_power(q):
                    consider(*lib.projective_plane_incidence(q))
                    break
            # Araujo-Pardo & Lopez record family when d-2 is a prime power >= 3.
            q2 = d - 2
            if q2 >= 3 and lib.is_prime_power(q2):
                try:
                    consider(*lib.araujo_lopez_graph(q2))
                except Exception:
                    pass
        elif D >= 4:
            # Smallest prime power q with q+1 >= d: W(q) has degree q+1 >= d.
            q = next(x for x in range(2, 10000) if lib.is_prime_power(x) and x + 1 >= d)
            if q <= 9:
                n_w, e_w = _gq_w(q)
                consider(n_w, e_w)  # valid directly when q+1 == d
                adj = _adjacency(n_w, e_w)
                n_best, alive_best = _sa(n_w, adj, d, D, deadline, rng)
                if alive_best is not None and n_best > best[0]:
                    n2, e2 = _induced(n_w, adj, alive_best)
                    consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
