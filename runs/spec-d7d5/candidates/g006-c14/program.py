import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (kept from the parent for D = 3 and D = 4).
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
# NEW CONSTRUCTION: bipartite Cayley graphs over semidirect products.
#
# Bi(G, S) has vertices (g, 0) and (g, 1) for g in G, and edges (g, 0)~(g*s, 1)
# for s in S, |S| = d. Left multiplication is an automorphism, so the diameter
# condition reduces to two breadth-first searches from the identity: one from
# (e, 0) and one from (e, 1) are not needed separately; a single BFS from (e, 0)
# over both layers suffices, because every vertex (a, x) is mapped to (e, x')
# by left multiplication, and distances from (e, 0) cover all same-side and
# cross-side pairs.
#
# The search is simulated annealing over the d-element generator set S, with
# cost = number of vertices not within distance D of (e, 0). This replaces the
# parent's multi-base voltage lifts with a single-orbit model whose cost is two
# BFS passes instead of a full all-pairs check.
# ----------------------------------------------------------------------------

_KS_ORDERS = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20]
_GCAP = 1300


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(300):
        k2 = rng.choice(_KS_ORDERS)
        m = max(2, -(-target // k2)) + rng.randrange(0, 3)
        if k2 == 1:
            return m, 1, 1
        if m < 3:
            continue
        for _ in range(80):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                return m, k2, c
    return None


def _tables(m, k2, r):
    """Return (G, MT, Back) for Z_m x| Z_k2.

    Element (a, b) is coded as a*k2 + b with (a, b)(c, e) = (a + r^b c, b + e).
    MT[s, g] = g*s and Back[s, h] = h*s^{-1}.
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    MT = np.ascontiguousarray(M.T)
    inv = np.argmax(M == 0, axis=1)  # identity has code 0
    Back = np.ascontiguousarray(MT[inv])
    return G, MT, Back


def _cost(S, G, MT, Back, D):
    """Number of vertices of Bi(G, S) not within distance D of (e, 0)."""
    V0 = np.zeros(G, dtype=bool)
    V1 = np.zeros(G, dtype=bool)
    V0[0] = True
    F = V0.copy()
    layer = 0
    for _ in range(D):
        idx = np.flatnonzero(F)
        if idx.size == 0:
            break
        if layer == 0:
            cand = np.concatenate([MT[s][idx] for s in S])
            new = np.zeros(G, dtype=bool)
            new[cand] = True
            new &= ~V1
            V1 |= new
            layer = 1
        else:
            cand = np.concatenate([Back[s][idx] for s in S])
            new = np.zeros(G, dtype=bool)
            new[cand] = True
            new &= ~V0
            V0 |= new
            layer = 0
        F = new
    return (G - int(V0.sum())) + (G - int(V1.sum()))


def _anneal(d, D, G, MT, Back, rng, deadline, iters):
    """Simulated annealing over the generator set S. Returns S (list) or None."""
    S = rng.sample(range(G), d)
    cost = _cost(S, G, MT, Back, D)
    c0 = float(max(cost, 1))
    for t in range(iters):
        if cost == 0:
            break
        if (t & 127) == 0 and time.monotonic() > deadline:
            break
        temp = max(0.3, 0.02 * c0 * (1.0 - t / iters))
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _cost(S, G, MT, Back, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[i] = old
    return list(S) if cost == 0 else None


def _edges_from(S, G, MT):
    """Edge list of Bi(G, S): (g, 0) ~ (g*s, 1), with side-1 vertices offset by G."""
    edges = []
    for s in S:
        hs = MT[s].tolist()
        edges.extend((g, G + h) for g, h in enumerate(hs))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
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

    # Exact constructions for small diameters.
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

    # Bi-Cayley annealing over semidirect products.
    best_G = best_n // 2
    while time.monotonic() < deadline:
        if best_G >= _GCAP:
            break
        target = best_G + 1 + rng.randrange(0, max(2, best_G // 12 + 1))
        target = min(target, _GCAP)
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, MT, Back = _tables(m, k2, r)
        if G <= best_G or G <= d or G > _GCAP + 200:
            continue
        S = _anneal(d, D, G, MT, Back, rng, deadline, 3000)
        if S is None:
            continue
        edges = _edges_from(S, G, MT)
        n = 2 * G
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n
            best_G = G

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
