"""Bipartite voltage lifts over non-cyclic groups for the d=10, D=5 target, with a Haar fallback.

CONSTRUCTION.  Take a base bipartite multigraph with k A-vertices and k B-vertices, circulant so that
every vertex has degree d: A_i is joined to B_j by m_ij = c[(j-i) mod k] darts, with sum(c) = d.
Each dart carries a group element g of G = Z_m x|_lam Z_k (order N = m*k).  Dart (A_i, B_j, g) gives
the edges (A_i, x) ~ (B_j, x*g) for all x in G.  The lift has 2*k*N vertices and is d-regular and
bipartite.  Left translation by h in G is an automorphism, so each fibre is one orbit and the diameter
is the largest eccentricity over the 2k base sources (identity of each fibre).  Simulated annealing
over the dart labels minimises the number of vertices left beyond distance D from those sources.
Cost 0 means valid.  Candidates have 2kN > 4000 vertices, so a success beats the record.

SAFETY.  Only a graph accepted by lib.is_valid is returned.  If no candidate reaches cost 0 in the
time budget, a valid Haar graph (3582 vertices) is returned.  Other (d, D) cases get a small valid graph.
"""
import math
import time

import numpy as np

import lib


TARGET = (10, 5)
TEMP = 0.8
PATIENCE = 1500
FB_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Small graph that is always valid for other (d, D) cases."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    g = lib.haar_graph(d, range(d))
    return g if lib.is_valid(g[0], g[1], d, D) else (1, [])


def haar_fallback(d, D):
    """Valid Haar graph on 2*1791 vertices (checked), or None."""
    try:
        m, k, lam = 199, 9, 180
        N = m * k
        pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
        g = np.arange(N, dtype=np.int64)
        a, j = g // k, g % k
        MT = ((a[:, None] + pw[j][:, None] * a[None, :]) % m) * k + (j[:, None] + j[None, :]) % k
        edges = []
        for s in FB_S:
            edges += [(int(x), int(N + MT[s, x])) for x in range(N)]
        n = 2 * N
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return None


def pick_lam(m, k):
    """An element lam of Z_m with lam^k = 1 mod m, preferring one of exact order k."""
    fallback = None
    for l in range(2, m):
        if math.gcd(l, m) == 1 and pow(l, k, m) == 1:
            if all(pow(l, j, m) != 1 for j in range(1, k)):
                return l
            if fallback is None:
                fallback = l
    return fallback


def candidates():
    """(k, m, lam) with 2*k*m*k > 4000 vertices, sorted by vertex count (closest to the record first)."""
    out = []
    for k, mr in ((2, range(501, 521)), (3, range(223, 235)), (5, range(81, 91))):
        for m in mr:
            N = m * k
            if 2 * k * N <= 4000:
                continue
            lam = pick_lam(m, k)
            if lam is None:
                continue
            out.append((2 * k * N, k, m, lam))
    out.sort()
    return [(k, m, lam) for _, k, m, lam in out]


def anneal(k, m, lam, d, D, deadline, rng):
    """Anneal dart labels for one (k, m, lam). Returns (n, edges) on a checked valid graph, else None."""
    N = m * k
    n = 2 * k * N
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    xa, xj = x // k, x % k
    sources = [u * N for u in range(2 * k)]

    def edges_of(DI, DJ, DG):
        G = DG[:, None]
        prod = ((xa[None, :] + pw[xj][None, :] * (G // k)) % m) * k + (xj[None, :] + G % k) % k
        A = (DI[:, None] * N + x[None, :]).ravel()
        B = ((k + DJ)[:, None] * N + prod).ravel()
        return A, B

    def nb_of(A, B):
        src = np.concatenate([A, B])
        tgt = np.concatenate([B, A])
        order = np.argsort(src, kind="stable")
        return tgt[order].reshape(n, d)

    def cost_of(nb):
        total = 0
        for s in sources:
            seen = np.zeros(n, dtype=bool)
            seen[s] = True
            frontier = np.array([s], dtype=np.int64)
            for _ in range(D):
                nbr = nb[frontier].ravel()
                nbr = nbr[~seen[nbr]]
                if nbr.size == 0:
                    break
                nbr = np.unique(nbr)
                seen[nbr] = True
                frontier = nbr
            total += n - int(seen.sum())
        return total

    def fresh():
        while True:
            c = np.bincount(rng.integers(0, k, size=d), minlength=k)
            if c.min() >= 1:
                break
        DI, DJ, DG = [], [], []
        for i in range(k):
            for j in range(k):
                cij = int(c[(j - i) % k])
                elems = rng.choice(N, size=cij, replace=False)
                DI += [i] * cij
                DJ += [j] * cij
                DG += [int(e) for e in elems]
        return (np.array(DI, dtype=np.int64), np.array(DJ, dtype=np.int64),
                np.array(DG, dtype=np.int64))

    while time.monotonic() < deadline:
        DI, DJ, DG = fresh()
        A, B = edges_of(DI, DJ, DG)
        nb = nb_of(A, B)
        cur = cost_of(nb)
        since = 0
        while time.monotonic() < deadline and since < PATIENCE and cur > 0:
            t = int(rng.integers(len(DG)))
            i, j = DI[t], DJ[t]
            same = DG[(DI == i) & (DJ == j)]
            while True:
                g = int(rng.integers(N))
                if not np.any(same == g):
                    break
            DG2 = DG.copy()
            DG2[t] = g
            A2, B2 = edges_of(DI, DJ, DG2)
            nb2 = nb_of(A2, B2)
            c2 = cost_of(nb2)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
                DG, nb, cur = DG2, nb2, c2
            if delta < 0:
                since = 0
            else:
                since += 1
        if cur == 0:
            A, B = edges_of(DI, DJ, DG)
            edges = list(zip(A.tolist(), B.tolist()))
            if lib.is_valid(n, edges, d, D):
                return n, edges
            return None
    return None


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.72 * time_limit
    rng = np.random.default_rng(seed)
    best = None
    cands = candidates()
    for idx, (k, m, lam) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        slot_end = now + (deadline - now) / (len(cands) - idx)
        try:
            res = anneal(k, m, lam, d, D, slot_end, rng)
        except Exception:
            res = None
        if res is not None and (best is None or res[0] > best[0]):
            best = res
    if best is not None:
        return best
    fb = haar_fallback(d, D)
    if fb is not None:
        return fb
    return trivial(d, D)
