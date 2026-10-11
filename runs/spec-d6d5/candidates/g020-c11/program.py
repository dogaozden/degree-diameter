import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline: projective plane incidence graph PG(2, q), q + 1 <= d.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: bi-Cayley (Haar-type) graphs over non-abelian groups.
#
# Group G = Z_m x| Z_k with multiplication table T. Vertices a_g = g and
# b_h = G + h. Connection set S (|S| = d, distinct group elements) gives
# edges a_g -- b_{g*s} for s in S. Every vertex then has degree d and the
# graph is bipartite.
#
# Left multiplication by any group element is an automorphism that preserves
# both sides. So every pair of vertices is within distance D iff every vertex
# is within distance D of a_e and of b_e (e = identity, index 0). Abelian
# groups are weak here because their sumsets collapse, so the search favours
# non-abelian groups.
# ----------------------------------------------------------------------------

def _table(m, k, r):
    """Multiplication table of Z_m x| Z_k, element (a, b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d)."""
    G = m * k
    X = np.arange(G, dtype=np.int64)
    a = X // k
    b = X % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    B = (b[:, None] + b[None, :]) % k
    return A * k + B


def _random_group(G, rng):
    """Return (m, k, r) with m*k = G, favouring non-abelian semidirect products."""
    ks = [k for k in range(1, G + 1) if G % k == 0]
    nonab = [k for k in ks if k >= 2 and G // k >= 2]
    if nonab and rng.random() < 0.8:
        k = rng.choice(nonab)
    else:
        k = rng.choice(ks)
    m = G // k
    if m == 1:
        return (1, k, 1)
    cands = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    if not cands:
        return (m, 1, 1)
    non_trivial = [r for r in cands if r != 1]
    if non_trivial and rng.random() < 0.8:
        r = rng.choice(non_trivial)
    else:
        r = rng.choice(cands)
    return (m, k, r)


def _reach(table, S, invS, G, D, startA):
    """Union of walk endpoints of length <= D from e on side A (startA) or side B."""
    cur = np.zeros(G, dtype=bool)
    cur[0] = True
    if startA:
        Aun = cur.copy()
        Bun = np.zeros(G, dtype=bool)
    else:
        Aun = np.zeros(G, dtype=bool)
        Bun = cur.copy()
    sideA = startA
    for _ in range(D):
        idx = np.flatnonzero(cur)
        cols = S if sideA else invS
        nxt = np.zeros(G, dtype=bool)
        nxt[table[np.ix_(idx, cols)].ravel()] = True
        if sideA:
            Bun |= nxt
        else:
            Aun |= nxt
        cur = nxt
        sideA = not sideA
    return Aun, Bun


def _cost(table, S, invS, G, D):
    """Number of (source, vertex) pairs not reached within D. Zero means diameter <= D."""
    c = 0
    for startA in (True, False):
        Aun, Bun = _reach(table, S, invS, G, D, startA)
        c += 2 * G - int(Aun.sum()) - int(Bun.sum())
    return c


def _anneal(table, inv, G, d, D, rng, end):
    """Simulated annealing over connection sets S of size d. Returns S (array) or None."""
    S = np.array(rng.sample(range(G), d), dtype=np.int64)
    c = _cost(table, S, inv[S], G, D)
    T = 1.0
    while c > 0:
        if time.monotonic() >= end:
            return None
        i = rng.randrange(d)
        x = rng.randrange(G)
        if (S == x).any():
            continue
        S2 = S.copy()
        S2[i] = x
        c2 = _cost(table, S2, inv[S2], G, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = S2, c2
        T = max(0.2, T * 0.9995)
    return S


def _graph_from(table, S, G):
    """Edges of the bi-Cayley graph: a_g = g, b_h = G + h, a_g -- b_{g*s}."""
    cols = table[:, S].ravel()
    rows = np.repeat(np.arange(G, dtype=np.int64), len(S))
    return [(int(g), int(G + c)) for g, c in zip(rows, cols)]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 5.0)
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2).
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

    moore = lib._moore_bound(d, D)
    if best_n >= moore:
        return best

    # Main search: bi-Cayley graphs over non-abelian groups, growing the order.
    G_lo = max(d, 2, best_n // 2 + 1)
    while time.monotonic() < deadline:
        G = G_lo + rng.randrange(0, 3)
        if 2 * G > moore or 2 * G <= best_n:
            G_lo = max(G_lo, best_n // 2 + 1)
            if 2 * G_lo > moore:
                break
            continue
        m, k, r = _random_group(G, rng)
        table = _table(m, k, r)
        inv = np.argmax(table == 0, axis=1).astype(np.int64)
        S = _anneal(table, inv, G, d, D, rng, min(deadline, time.monotonic() + 1.2))
        if S is not None:
            consider(2 * G, _graph_from(table, S, G))
            G_lo = max(G_lo, G + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
