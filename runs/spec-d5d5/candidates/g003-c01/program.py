import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (valid for smaller D or d; used as fallbacks).
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New main construction: Haar graphs of non-abelian groups.
#
# H(G, S) has vertices A_g and B_h (g, h in G), with A_g ~ B_{g*s} for s in S,
# |S| = d. It is bipartite and d-regular with 2|G| vertices. Left translation is
# an automorphism that preserves each side, so the diameter is at most D iff a
# BFS of depth D from A_e and from B_e reaches everything.
#
# Search: pick a group of order G (mostly non-abelian semidirect products
# Z_m x| Z_k), then run a annealed local search over the connection set S,
# minimising the number of unreached (source, vertex) pairs.
# ----------------------------------------------------------------------------

def _moore_even(d, D):
    """Moore-type bound 2 * sum_{i<D} (d-1)^i for bipartite graphs."""
    return 2 * sum((d - 1) ** i for i in range(D))


def _sample_group(G, rng):
    """Return (order, mul) for a group of order G, preferring non-abelian semidirect products."""
    divs = [k for k in range(2, G) if G % k == 0 and G // k >= 3]
    for _ in range(40):
        if divs and rng.random() < 0.8:
            k = rng.choice(divs)
            m = G // k
            r = None
            for _ in range(200):
                cand = rng.randrange(2, m)
                if math.gcd(cand, m) == 1 and pow(cand, k, m) == 1 % m:
                    r = cand
                    break
            if r is None:
                continue
            order, mul, _ = lib.semidirect_group(m, k, r)
            return order, mul
        break
    order, mul, _ = lib.semidirect_group(G, 1, 1)
    return order, mul


def _search_haar(d, D, G_target, rng, deadline, budget=1500):
    """Try to find a Haar graph H(G, S) with |G| = order near G_target and diameter <= D.

    Returns (n, edges) on success, otherwise None.
    """
    g = _sample_group(G_target, rng)
    if g is None:
        return None
    order, mul = g
    if order < d + 1:
        return None

    cache = {}

    def pq(s):
        """Forward map g -> g*s and its inverse, cached per element s."""
        if s not in cache:
            P = [mul(x, s) for x in range(order)]
            Q = [0] * order
            for x, y in enumerate(P):
                Q[y] = x
            cache[s] = (P, Q)
        return cache[s]

    N = 2 * order

    def cost_of(S):
        """Number of (source, vertex) pairs not reached within distance D from A_e and B_e."""
        Pm = [pq(s)[0] for s in S]
        Qm = [pq(s)[1] for s in S]
        total = 0
        for src in (0, order):
            seen = bytearray(N)
            seen[src] = 1
            frontier = [src]
            count = 1
            for _ in range(D):
                nxt = []
                for u in frontier:
                    if u < order:
                        for P in Pm:
                            v = order + P[u]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                    else:
                        h = u - order
                        for Q in Qm:
                            v = Q[h]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                count += len(nxt)
                frontier = nxt
                if not frontier:
                    break
            total += N - count
        return total

    S = rng.sample(range(order), d)
    cur = cost_of(S)
    for it in range(budget):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        s_new = rng.randrange(order)
        if s_new in S:
            continue
        S2 = S[:]
        S2[i] = s_new
        c2 = cost_of(S2)
        T = max(0.15, 2.0 * (1.0 - it / budget))
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            S, cur = S2, c2

    if cur != 0:
        return None
    edges = []
    for s in S:
        P = pq(s)[0]
        for x in range(order):
            edges.append((x, order + P[x]))
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Nothing can beat the bound: return immediately (e.g. calibration cases).
    if d >= 3 and best_n >= _moore_even(d, D):
        return best

    # Main search: Haar graphs over non-abelian groups, climbing one order at a time.
    best_G = best_n // 2
    while time.monotonic() < deadline:
        target = best_G + 1
        if rng.random() < 0.3:
            target += rng.randrange(0, 6)
        res = _search_haar(d, D, target, rng, deadline)
        if res is not None:
            n, e = res
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
                best_G = n // 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
