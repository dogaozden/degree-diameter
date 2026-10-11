import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (exact constructions for small cases).
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
# NEW construction: bipartite double of Cayley graphs (bi-Cayley with one base
# pair), searched by simulated annealing over the connection set.
#
# Group G = Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e)).
# Vertices: side-0 g  ->  id g,   side-1 h  ->  id G+h.
# Edges:    (g, 0) ~ (g*s, 1) for every s in S, |S| = d.
# Left multiplication is an automorphism preserving sides, so the diameter
# check only needs BFS from (e,0) and (e,1). Cost = number of unreached
# (source, target) pairs; cost 0 means diameter <= D and the graph is valid.
# Unlike the parent's layered voltage lifts, this uses one base pair and
# searches over many group orders near (and above) the record.
# ----------------------------------------------------------------------------

_MAX_G = 1200


def _group_table(m, k2, r):
    """Return (G, M, inv): multiplication table M[x, y] and inverse array for Z_m x| Z_k2."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    inv = np.argmax(M == 0, axis=1)  # identity is index 0
    return G, M, inv


def _sample_group(G, rng):
    """Return (m, k2, r) with m * k2 = G, chosen at random among factorizations."""
    divs = [k for k in range(1, 41) if G % k == 0 and G // k >= 2]
    k2 = rng.choice(divs)
    m = G // k2
    r = 1
    if k2 == 2 and rng.random() < 0.3:
        r = m - 1  # dihedral-type
    elif k2 > 1 and m > 2:
        for _ in range(60):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
    if math.gcd(r, m) != 1 or pow(r, k2, m) != 1 % m:
        r = 1
    return m, k2, r


def _unreached(G, M, inv, S, D):
    """Number of unreached (source, target) pairs among the 4G pairs from the two sources."""
    V0 = np.zeros((2, G), dtype=bool)  # V0[s, g]: side-0 vertex g within current radius of source s
    V1 = np.zeros((2, G), dtype=bool)  # V1[s, h]: side-1 vertex h within current radius of source s
    V0[0, 0] = True  # source 0 is (e, 0)
    V1[1, 0] = True  # source 1 is (e, 1)
    Rm = [M[:, s] for s in S]          # side 0 g -> side 1 g*s
    Ri = [M[:, inv[s]] for s in S]     # side 1 h -> side 0 h*s^{-1}
    for _ in range(D):
        n1 = V1.copy()
        n0 = V0.copy()
        for p in Rm:
            n1[:, p] |= V0
        for p in Ri:
            n0[:, p] |= V1
        V0, V1 = n0, n1
    return 4 * G - int(V0.sum()) - int(V1.sum())


def _anneal(G, M, inv, d, D, rng, deadline, iters):
    """Simulated annealing over d-subsets of Z_G; returns the connection set or None."""
    S = rng.sample(range(G), d)
    cost = _unreached(G, M, inv, S, D)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.25, 4.0 * (1.0 - t / iters))
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _unreached(G, M, inv, S, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[i] = old
    if cost == 0:
        return list(S)
    return None


def _graph_from(G, M, S):
    """Edges of the bipartite double of Cayley(G, S)."""
    gs = M[:, S]  # gs[g, j] = g * S[j]
    u = np.repeat(np.arange(G, dtype=np.int64), len(S))
    v = G + gs.reshape(-1)
    return 2 * G, list(zip(u.tolist(), v.tolist()))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 3.0)
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

    # Exact constructions for small cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley search. Target group orders around a fixed fraction of the Moore bound
    # (about 0.365 for d=7, D=5, where the record is 1134 = 2*567).
    moore = lib._moore_bound(d, D)
    base_lo = int(0.365 * moore / 2)
    if base_lo <= _MAX_G and time.monotonic() < deadline:
        while time.monotonic() < deadline:
            lo = max(base_lo, best_n // 2 + 1, d + 1)
            if lo > _MAX_G:
                break
            G = rng.randrange(lo, min(lo + 40, _MAX_G) + 1)
            m, k2, r = _sample_group(G, rng)
            G, M, inv = _group_table(m, k2, r)
            if G < d + 1:
                continue
            S = _anneal(G, M, inv, d, D, rng, deadline, 3000)
            if S is not None:
                n2, e2 = _graph_from(G, M, S)
                consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
