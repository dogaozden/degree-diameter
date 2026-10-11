import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / calibration constructions (cheap, used as the safe floor).
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
# New construction: k = 1 bi-Cayley graphs over finite groups.
#
# Group G (order m*k) is Z_m x| Z_k with action r, or a direct/cyclic product.
# Vertices A_g = g and B_h = G + h. Connection set S = {s_1..s_d} subset of G:
#     A_g ~ B_{g*s}   for every s in S.
# Every vertex has degree exactly d and the graph is bipartite and simple.
# Left multiplication is an automorphism, so the diameter condition reduces to
# two BFS trees: from A_1 and from B_1. A simulated annealing search chooses S
# to minimise the number of (source, vertex) pairs at distance > D.
# Groups of order just above (best_n / 2) are tried in turn.
# ----------------------------------------------------------------------------

def _table(m, k, r):
    """Multiplication table M[x, y] of Z_m x| Z_k (element a*k+b, (a,b)(c,e) = (a + r^b c, b + e))."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    powers = np.array([pow(r, t, m) if m > 1 else 0 for t in range(k)], dtype=np.int64)
    top = (a[:, None] + powers[b][:, None] * a[None, :]) % m
    return top * k + (b[:, None] + b[None, :]) % k


def _random_group(G, rng):
    """Multiplication table of a randomly chosen semidirect product of order G."""
    divs = [k for k in range(1, G + 1) if G % k == 0]
    k = rng.choice(divs)
    m = G // k
    if m == 1:
        r = 0
    else:
        cands = [u for u in range(1, m)
                 if math.gcd(u, m) == 1 and pow(u, k, m) == 1 % m]
        r = rng.choice(cands) if cands else 1
    return _table(m, k, r)


def _anneal(d, D, G, M, rng, deadline, iters):
    """Search a connection set S of size d in the group with table M. Returns edges or None."""
    N = 2 * G
    ar = np.arange(G, dtype=np.int64)
    S = rng.sample(range(G), d)
    P = np.empty((d, G), dtype=np.int64)   # P[i, g] = g * s_i
    Q = np.empty((d, G), dtype=np.int64)   # Q[i, h] = g with g * s_i = h
    nbr = np.empty((d, N), dtype=np.int64)

    def load(i, s):
        p = M[:, s]
        P[i] = p
        Q[i, p] = ar
        nbr[i, :G] = G + p
        nbr[i, G:] = Q[i]

    for i, s in enumerate(S):
        load(i, s)

    def evaluate():
        reach = np.zeros(N, dtype=np.int64)
        reach[0] = 1          # source A_1, bit 0
        reach[G] = 2          # source B_1, bit 1
        for _ in range(D):
            new = reach.copy()
            for i in range(d):
                new |= reach[nbr[i]]
            if np.array_equal(new, reach):
                break
            reach = new
        cov = int(np.count_nonzero(reach & 1)) + int(np.count_nonzero(reach & 2))
        return 2 * N - cov

    cost = evaluate()
    for t in range(iters):
        if cost == 0:
            break
        if (t & 63) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old_row = nbr[i].copy()
        old_p = P[i].copy()
        old_q = Q[i].copy()
        old_s = S[i]
        load(i, new)
        c2 = evaluate()
        temp = 0.3 + 2.0 * (1.0 - t / iters)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            S[i] = new
            cost = c2
        else:
            nbr[i] = old_row
            P[i] = old_p
            Q[i] = old_q
            S[i] = old_s

    if cost != 0:
        return None
    us = np.repeat(ar, d)
    vs = G + P.T.reshape(-1)
    return list(zip(us.tolist(), vs.tolist()))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 5.0))
    deadline = start + budget
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

    try:
        # Exact constructions.
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best

        if D == 4 and time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
                if d - 1 <= 9 and lib.is_prime_power(d - 1):
                    return best

        # Main search: bi-Cayley lifts over groups of order just above best_n / 2.
        if d >= 2 and D >= 2:
            iters = 4000
            while time.monotonic() < deadline:
                G = max(d, best_n // 2 + 1 + rng.randrange(0, 4))
                M = _random_group(G, rng)
                edges = _anneal(d, D, G, M, rng, deadline, iters)
                if edges is not None:
                    consider(2 * G, edges)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
