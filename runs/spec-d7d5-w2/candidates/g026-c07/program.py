import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baseline: incidence graph of PG(2, q), q the largest prime power <= d-1.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: bipartite Cayley graphs over finite groups.
#
# Group G (order G_n) with elements 0..G_n-1, multiplication table M[g, h] = g*h,
# identity 0. Connection set S = {s_1..s_d} of distinct elements.
# Vertices: side 0 = g (id g), side 1 = G_n + g (id G_n + g).
# Edges: (g, 0) ~ (g*s, 1) for every s in S.
# Degree is exactly d on both sides, the graph is bipartite, and left
# translations act transitively on each side. So diameter <= D holds iff the
# balls of radius D around (e,0) and (e,1) cover everything. That is checked
# with a numpy BFS, which makes each evaluation cheap.
# The search is simulated annealing over S, minimising the number of unreached
# (start, vertex) pairs.
# Groups are semidirect products Z_m x| Z_k (r = 1 gives the abelian case).
# ----------------------------------------------------------------------------

def _divisors(n):
    return [k for k in range(1, n + 1) if n % k == 0]


def _sample_group(G, rng):
    """Return (m, k, r) with m*k = G and r^k = 1 mod m, gcd(r, m) = 1."""
    divs = _divisors(G)
    k = rng.choice(divs)
    m = G // k
    if k == 1 or m <= 2:
        return m, k, 1
    for _ in range(80):
        c = rng.randrange(1, m)
        if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
            return m, k, c
    return m, k, 1  # abelian fallback, always valid


def _group_table(m, k, r):
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    # (a, b)(c, e) = (a + r^b c, b + e), coded as a*k + b.
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    return M


def _unreached(M, S, Sinv, G, D):
    """Number of (start, vertex) pairs at distance > D, for starts (e,0) and (e,1)."""
    total = 0
    for start in (0, 1):
        seen = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        f = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        seen[start][0] = True
        f[start][0] = True
        for _ in range(D):
            new0 = np.zeros(G, dtype=bool)
            new1 = np.zeros(G, dtype=bool)
            idx0 = np.flatnonzero(f[0])
            idx1 = np.flatnonzero(f[1])
            if idx0.size:
                new1[M[np.ix_(idx0, S)].ravel()] = True
            if idx1.size:
                new0[M[np.ix_(idx1, Sinv)].ravel()] = True
            new1 &= ~seen[1]
            new0 &= ~seen[0]
            seen[0] |= new0
            seen[1] |= new1
            f = [new0, new1]
            if not (new0.any() or new1.any()):
                break
        total += 2 * G - int(seen[0].sum()) - int(seen[1].sum())
    return total


def _anneal(M, invtab, G, d, D, rng, deadline, iters):
    """Return a connection set S (list of d distinct elements) with zero cost, or None."""
    S = rng.sample(range(G), d)
    Sinv = [int(invtab[s]) for s in S]
    cost = _unreached(M, S, Sinv, G, D)
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.3, 3.0 * (1.0 - t / iters))
        pos = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[pos]
        old_inv = Sinv[pos]
        S[pos] = new
        Sinv[pos] = int(invtab[new])
        c2 = _unreached(M, S, Sinv, G, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[pos] = old
            Sinv[pos] = old_inv
    if cost != 0:
        return None
    return S


def _to_graph(M, G, S):
    edges = []
    for s in S:
        col = M[:, s].tolist()
        edges.extend((g, G + int(t)) for g, t in enumerate(col))
    return 2 * G, edges


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Search window for the group order G (the graph has 2G vertices).
    if d == 7 and D == 5:
        lo, hi = 568, 700  # aim above the record 1134 = 2 * 567
    else:
        lo = best_n // 2 + 1
        hi = lo + max(16, lo // 8)

    while time.monotonic() < deadline - 1.0:
        G = rng.randint(lo, hi)
        m, k, r = _sample_group(G, rng)
        M = _group_table(m, k, r)
        invtab = np.argmax(M == 0, axis=1)
        S = _anneal(M, invtab, G, d, D, rng, deadline, 3000)
        if S is not None:
            n, e = _to_graph(M, G, S)
            consider(n, e)
            # Climb: look for larger groups after a success.
            lo = max(lo, G + 1)
            hi = max(hi, lo + 8)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
