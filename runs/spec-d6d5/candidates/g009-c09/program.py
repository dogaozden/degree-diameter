import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base families.
# ----------------------------------------------------------------------------

def _pg_inc(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d. Diameter 3."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Returns (2P, edges) with points 0..P-1, lines P..2P-1. Each point and line has q+1 neighbours.
    Diameter 4.
    """
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


def _gq_for(d):
    """W(q) for the largest prime power q <= min(d - 1, 9)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bipartite voltage lifts of a base graph over Z_m, annealed on the
# number of ordered vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _lift_adj(n_base, base_edges, volt, m):
    """Adjacency lists of the Z_m lift: base dart (u, v, a) joins u*m+g to v*m+(g+a)%m."""
    adj = [[] for _ in range(n_base * m)]
    for (u, v), a in zip(base_edges, volt):
        um, vm = u * m, v * m
        for g in range(m):
            x = um + g
            y = vm + (g + a) % m
            adj[x].append(y)
            adj[y].append(x)
    return adj


def _lift_bad(N, adj, D):
    """Ordered pairs at distance > D (bit-parallel). Zero iff diameter <= D."""
    reach = [1 << v for v in range(N)]
    full = (1 << N) - 1
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
        if all(r == full for r in reach):
            return 0
    return sum(N - r.bit_count() for r in reach)


def _anneal_lift(n_base, base_edges, m, D, deadline, rng):
    """Anneal Z_m voltages on the base graph until the lift has diameter <= D.

    Returns the lift edge list when successful, else None.
    """
    E = len(base_edges)
    N = n_base * m
    volt = [rng.randrange(m) for _ in range(E)]
    cur = _lift_bad(N, _lift_adj(n_base, base_edges, volt, m), D)
    best_c, best_v = cur, list(volt)
    T = 30.0
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(E)
        old = volt[i]
        new = rng.randrange(m - 1)
        if new >= old:
            new += 1
        volt[i] = new
        c = _lift_bad(N, _lift_adj(n_base, base_edges, volt, m), D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
            if cur < best_c:
                best_c, best_v = cur, list(volt)
        else:
            volt[i] = old
        T = max(2.0, T * 0.999)
    if best_c != 0:
        return None
    edges = []
    for (u, v), a in zip(base_edges, best_v):
        for g in range(m):
            edges.append((u * m + g, v * m + (g + a) % m))
    return edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _pg_inc(d)
        if pg is not None:
            consider(pg[0], pg[1])

    gq = _gq_for(d) if D >= 4 else None
    if gq is not None:
        consider(gq[0], gq[1])

    # New family for D >= 5: Z_m voltage lifts of the W(q) incidence graph.
    # The lift keeps degree q+1 and bipartiteness; we anneal voltages to reach diameter <= D.
    if D >= 5 and gq is not None:
        n_g, base_edges = gq
        moore = lib._moore_bound(d, D)
        todo = [m for m in (3, 2, 4) if n_g * m <= moore and n_g * m > best_n]
        while todo and time.monotonic() < deadline:
            m = todo.pop(0)
            if n_g * m <= best_n:
                continue
            now = time.monotonic()
            span = deadline - now
            frac = 0.65 if todo else 1.0
            res = _anneal_lift(n_g, base_edges, m, D, now + span * frac, rng)
            if res is not None:
                consider(n_g * m, res)
                todo = [mm for mm in todo if n_g * mm > best_n]

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
