import math
import random
import time

import numpy as np

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _moore_half(d, D):
    """Half of the bipartite Moore bound: sum of (d-1)^i for i < D."""
    return sum((d - 1) ** i for i in range(D))


def _semidirect_options(G):
    """All (m, k, r) with m * k = G giving Z_m x| Z_k (r = 1 means direct product)."""
    opts = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _group_tables(m, k, r):
    """Multiplication table T (G x G) and inverse array for Z_m x| Z_k; identity is code 0."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    T = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    rows, cols = np.nonzero(T == 0)
    INV = np.zeros(G, dtype=np.int64)
    INV[rows] = cols
    return G, T, INV


def _cost(T, G, D, S, Sinv):
    """Number of (source, vertex) pairs not reached within D, from A_e and from B_e.

    The bi-Cayley graph has A_g ~ B_{g s} for s in S. Left multiplication is an
    automorphism transitive on each side, so these two sources decide the diameter.
    """
    Sa = np.asarray(S, dtype=np.int64)
    Si = np.asarray(Sinv, dtype=np.int64)
    cost = 0
    for side in (0, 1):
        seenA = np.zeros(G, dtype=bool)
        seenB = np.zeros(G, dtype=bool)
        empty = np.zeros(0, dtype=np.int64)
        if side == 0:
            seenA[0] = True
            fA = np.array([0], dtype=np.int64)
            fB = empty
        else:
            seenB[0] = True
            fA = empty
            fB = np.array([0], dtype=np.int64)
        for _ in range(D):
            if fA.size == 0 and fB.size == 0:
                break
            nB = np.zeros(G, dtype=bool)
            nA = np.zeros(G, dtype=bool)
            if fA.size:
                nB[T[fA][:, Sa].ravel()] = True
            if fB.size:
                nA[T[fB][:, Si].ravel()] = True
            nB &= ~seenB
            nA &= ~seenA
            seenB |= nB
            seenA |= nA
            fA = np.flatnonzero(nA)
            fB = np.flatnonzero(nB)
        cost += 2 * G - int(seenA.sum()) - int(seenB.sum())
    return cost


def _inv_list(INV, S):
    return [int(INV[s]) for s in S]


def _anneal(T, G, D, d, INV, rng, deadline):
    """Simulated annealing over the d-1 non-identity elements of S (identity WLOG in S).

    Returns (S, 0) on success or (None, cost) when the deadline passes.
    """
    S = [0] + rng.sample(range(1, G), d - 1)
    Sinv = _inv_list(INV, S)
    c = _cost(T, G, D, S, Sinv)
    temp = 1.5
    it = 0
    while c > 0:
        it += 1
        if (it & 31) == 0 and time.monotonic() > deadline:
            return None, c
        i = rng.randrange(1, d)
        new = rng.randrange(1, G)
        if new in S:
            continue
        S2 = S[:]
        S2[i] = new
        S2inv = _inv_list(INV, S2)
        c2 = _cost(T, G, D, S2, S2inv)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            S, Sinv, c = S2, S2inv, c2
        temp = max(0.15, temp * 0.9995)
    return S, 0


def _edges(T, G, S):
    """Edge list of the bi-Cayley graph: A_g = g, B_x = G + x, A_g ~ B_{g s}."""
    Sa = np.asarray(S, dtype=np.int64)
    targets = T[:, Sa].tolist()
    E = []
    for g in range(G):
        for t in targets[g]:
            E.append((g, G + int(t)))
    return 2 * G, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.2, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            # Calibration: PG(2, d-1) meets the Moore bound when d-1 is a prime power.
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Bold change: bi-Cayley graphs over non-abelian groups Z_m x| Z_k with one
    # vertex per side, found by annealing the connection set S (|S| = d).
    if d >= 3 and D >= 3:
        G = max(d, best[0] // 2 + 1, int(0.42 * _moore_half(d, D)))
        while time.monotonic() < deadline:
            for _ in range(2):
                if time.monotonic() >= deadline:
                    break
                opts = _semidirect_options(G)
                if not opts:
                    break
                m, k, r = rng.choice(opts)
                Gg, T, INV = _group_tables(m, k, r)
                slice_end = min(deadline, time.monotonic() + 2.5)
                S, _c = _anneal(T, Gg, D, d, INV, rng, slice_end)
                if S is not None:
                    n, e = _edges(T, Gg, S)
                    consider(n, e)
                    break
            G = max(G + 1, best[0] // 2 + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
