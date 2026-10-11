import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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


# ----------------------------------------------------------------------------
# Cayley bipartite graphs over small groups (the new D >= 4 construction).
#
# Vertices: x (side 0) and G + x (side 1), for x in the group of order G.
# Edges: x -- G + mul(x, s) for s in S, |S| = d.  Left multiplication is an
# automorphism, so only the balls around the identity on each side matter.
# ----------------------------------------------------------------------------

def _divisors(n):
    return [k for k in range(1, n + 1) if n % k == 0]


def _sample_group(G, rng):
    """Random group of order G as (order, mul): cyclic or Z_m x| Z_k with small k."""
    ks = [k for k in _divisors(G) if k <= 12]
    rng.shuffle(ks)
    for k in ks:
        m = G // k
        if m < 2:
            continue
        if k == 1:
            order, mul, _ = lib.cyclic_group(G)
            return order, mul
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not cands:
            continue
        r = rng.choice(cands)
        order, mul, _ = lib.semidirect_group(m, k, r)
        return order, mul
    return None


def _cost(G, mul, S, D):
    """Number of vertices missed by the radius-D balls of the identity on each side."""
    N = 2 * G
    adj = [[] for _ in range(N)]
    for x in range(G):
        for s in S:
            y = G + mul(x, s)
            adj[x].append(y)
            adj[y].append(x)
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _search_cayley(G, d, D, rng, deadline):
    """Random restarts of hill-climbing on the connection set S; returns (n, edges) or None."""
    while time.monotonic() < deadline:
        g = _sample_group(G, rng)
        if g is None:
            return None
        order, mul = g
        if order < d:
            continue
        S = rng.sample(range(order), d)
        c = _cost(order, mul, S, D)
        stall = 0
        while c > 0 and time.monotonic() < deadline and stall < 3000:
            i = rng.randrange(d)
            x = rng.randrange(order)
            if x in S:
                stall += 1
                continue
            T = S[:]
            T[i] = x
            ct = _cost(order, mul, T, D)
            if ct <= c or rng.random() < 0.01:
                S, c = T, ct
                stall = 0
            else:
                stall += 1
        if c == 0:
            n = 2 * order
            edges = [(x, order + mul(x, s)) for x in range(order) for s in S]
            return n, edges
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        return best if lib.is_valid(best[0], best[1], d, D) else lib.haar_graph(d, range(d))

    if D == 2:
        return best

    # D >= 4: generalized quadrangle base, then Cayley search.
    qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)]
    if qs:
        gq = _gq_w(qs[0])
        consider(gq[0], gq[1])

    moore = lib.moore_bound(d, D)
    main_end = start + 0.85 * time_limit
    lo_G = best_n // 2 + 1
    hi_G = moore // 2

    while time.monotonic() < main_end and lo_G <= hi_G:
        span = min(hi_G - lo_G + 1, 30)
        G = lo_G + rng.randrange(span)
        attempt_end = min(main_end, time.monotonic() + max(2.0, 0.08 * time_limit))
        res = _search_cayley(G, d, D, rng, attempt_end)
        if res is not None:
            consider(res[0], res[1])
            lo_G = max(lo_G, best_n // 2 + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
