"""Bi-Cayley lifts over semidirect products Z_m x| Z_k, searched by annealing.

For k = 1 the graph is a Cayley-type bipartite graph on a group G: A_g ~ B_{g*s} for s in S,
|S| = d. Left multiplication is an automorphism, so the diameter check only needs two
representatives (A_1 and B_1). The connection set is normalised to contain the identity.
The search anneals over S and walks a ladder of group orders just above the current best.
Every candidate is verified with lib.is_valid, and K_{d,d} is the fallback.
"""
import math
import random
import time

import numpy as np

import lib

_POP = np.array([0, 1, 1, 2], dtype=np.int64)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, kept small for speed."""
    for q in range(min(d - 1, 40), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group(m, k, r):
    """Z_m x| Z_k with element (a, b) coded as a*k + b and (a,b)(c,e) = (a + r^b c, b + e).

    Returns (G, M, inv): M[x, y] = x*y, and inv[x] is the inverse of x. Identity is index 0.
    """
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = np.argmax(M == 0, axis=1).astype(np.int64)
    return G, M, inv


def _groups_of(G, rng):
    """All (m, k, r) with m * k = G giving semidirect products (a few random r per order)."""
    out = []
    for k in range(1, 31):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if len(rs) > 4:
            rs = rng.sample(rs, 4)
        out.extend((m, k, r) for r in rs)
    return out


def _anneal(d, D, G, M, inv, rng, stop, max_evals):
    """Anneal over connection sets S (identity fixed in S[0]). Returns S with diameter <= D, or None."""
    N = 2 * G
    if G < d or d < 2:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    nbr = np.empty((d, N), dtype=np.int64)

    def set_layer(l, s):
        nbr[l, :G] = G + M[:, s]          # A_g ~ B_{g s}
        nbr[l, G:] = M[:, inv[s]]         # B_h ~ A_{h s^-1}

    for l, s in enumerate(S):
        set_layer(l, s)

    def cost_now():
        reach = np.zeros(N, dtype=np.int64)
        reach[0] = 1   # bit 0: source A_1
        reach[G] = 2   # bit 1: source B_1
        for _ in range(D):
            new = reach | np.bitwise_or.reduce(reach[nbr], axis=0)
            if np.array_equal(new, reach):
                break
            reach = new
        return 2 * N - int(_POP[reach].sum())

    cost = cost_now()
    evals = 0
    while cost > 0 and evals < max_evals and time.monotonic() < stop:
        evals += 1
        frac = evals / max_evals
        temp = 0.25 + 3.0 * (1.0 - frac)
        l = rng.randrange(1, d)
        new = rng.randrange(1, G)
        if new in S:
            continue
        old = S[l]
        S[l] = new
        set_layer(l, new)
        c2 = cost_now()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[l] = old
            set_layer(l, old)
    if cost != 0:
        return None
    return S


def _edges(G, M, S):
    e = []
    for s in S:
        col = (G + M[:, s]).tolist()
        e.extend((g, col[g]) for g in range(G))
    return 2 * G, e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D <= 0:
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

    if D == 2:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        return best

    moore = lib.moore_bound(d, D)

    try:
        while time.monotonic() < deadline and d >= 2:
            floor = int(0.3 * moore / 2)
            T = max(best_n // 2 + 1, floor)
            G = T + rng.randrange(0, 6)
            if G > 3000:
                break
            cand = _groups_of(G, rng)
            if not cand:
                continue
            m, k, r = rng.choice(cand)
            Gg, M, inv = _group(m, k, r)
            stop = min(deadline, time.monotonic() + 8.0)
            S = _anneal(d, D, Gg, M, inv, rng, stop, 60000)
            if S is not None:
                n, e = _edges(Gg, M, S)
                consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
