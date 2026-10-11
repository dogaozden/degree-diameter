import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Construction: bi-Cayley (Haar-type) graph H(G, S) over a group G of order n/2.
#
# Vertices: A_g = g and B_h = G + h. Edge A_g ~ B_{g*s} for each s in S, |S| = d.
# Every vertex has degree d and no duplicate edges arise since S has distinct
# elements. Left multiplication by x maps A_g -> A_{xg}, B_h -> B_{xh}, so
# diameter <= D reduces to two BFS runs, one from A_e and one from B_e.
#
# Groups are semidirect products Z_m x| Z_k (element a*k+b, (a,b)(c,e) = (a+r^b c, b+e)),
# which include the cyclic and direct-product cases. The connection set S is
# optimised by simulated annealing on the number of unreached pairs.
# This differs from the multi-block layered lifts used by the parent.
# ----------------------------------------------------------------------------


def _group_table(m, k, r):
    """Full multiplication table of Z_m x| Z_k with element index a*k+b; identity is index 0."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    A = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    return A


def _sample_group(order, rng):
    """Return (m, k, r) with m*k == order, choosing k among small divisors and r at random."""
    divs = [k for k in range(1, min(order, 16) + 1) if order % k == 0]
    k = rng.choice(divs)
    m = order // k
    r = 1 % m
    if k > 1 and m > 2 and rng.random() < 0.8:
        for _ in range(200):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                r = c
                break
    return m, k, r


def _cost(G, D, A, inv, S):
    """Number of (source, vertex) pairs unreached within D, for sources A_e and B_e."""
    d = len(S)
    Sa = np.asarray(S, dtype=np.int64)
    Sinv = inv[Sa]
    NB = np.empty((2 * G, d), dtype=np.int64)
    NB[:G] = G + A[:, Sa]
    NB[G:] = A[:, Sinv]
    unr = 0
    for src in (0, G):
        vis = np.zeros(2 * G, dtype=bool)
        vis[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(D):
            nx = NB[fr].ravel()
            nx = np.unique(nx[~vis[nx]])
            if nx.size == 0:
                break
            vis[nx] = True
            fr = nx
        unr += 2 * G - int(vis.sum())
    return unr


def _anneal(G, d, D, A, inv, rng, deadline, max_iter=20000):
    """Simulated annealing over connection sets S of size d. Returns S or None."""
    S = rng.sample(range(G), d)
    cost = _cost(G, D, A, inv, S)
    c0 = float(max(cost, 1))
    for t in range(max_iter):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _cost(G, D, A, inv, S)
        temp = max(0.3, 0.02 * c0 * (1.0 - t / max_iter))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[i] = old
    return S if cost == 0 else None


def _haar_edges(G, A, S):
    """Edge list of the bi-Cayley graph with A_g ~ B_{g*s}."""
    edges = []
    for s in S:
        col = A[:, s]
        for g in range(G):
            edges.append((g, G + int(col[g])))
    return 2 * G, edges


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Exact D = 3 construction when d - 1 is a prime power (calibration case).
    if D == 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best_n, best_e

    # Main search: bi-Cayley graphs over groups of growing order.
    G = max(d, best_n // 2 + 1)
    attempt_slice = max(1.0, 0.25 * budget)
    while time.monotonic() < deadline - 0.5:
        try:
            m, k, r = _sample_group(G, rng)
            A = _group_table(m, k, r)
            inv = np.argmax(A == 0, axis=1)
            slice_end = min(deadline, time.monotonic() + attempt_slice)
            S = _anneal(G, d, D, A, inv, rng, slice_end)
        except Exception:
            S = None
        if S is not None:
            n, e = _haar_edges(G, A, S)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_e = n, e
                G = best_n // 2 + 1
                continue
        # Failure: retry at the same order with a new group and connection set.

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
