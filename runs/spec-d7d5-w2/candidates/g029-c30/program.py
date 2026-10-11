import math
import random
import time

import numpy as np

import lib

# Bold pivot: instead of the mixed annealing over multi-block lifts, this version
# searches only single-orbit bi-Cayley (Haar-type) graphs. The graph is
#   A_x ~ B_{x*s} for s in S,  |S| = d,  x, s in a group G of order ~ 560-1200,
# with the group a semidirect product Z_m x| Z_k (r = 1 gives an abelian group).
# Left multiplication is an automorphism, so only two BFS runs (from A_0 and B_0)
# are needed to certify diameter D. S is normalised to contain the identity, which
# is WLOG. The search fixes the group order and moves one element of S at a time to
# reduce the number of vertices unreachable within D from A_0 and B_0.
# Every success is re-checked with lib.is_valid. K_{d,d} is the fallback.


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k, r) with m*k >= target describing Z_m x| Z_k (r = 1 gives Z_m x Z_k)."""
    ks = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24]
    for _ in range(100):
        k = rng.choice(ks)
        m = max(2, -(-target // k))
        if k == 1:
            return m, 1, 1
        if rng.random() < 0.4:
            return m, k, 1
        r = None
        for _ in range(80):
            c = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                r = c
                break
        if r is not None:
            return m, k, r
    return target, 1, 1


def _group(m, k, r):
    """Multiplication table Mul[x, y] = x*y and inverse array for (a,b)(c,e) = (a + r^b c, b + e)."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    Mul = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = np.empty(G, dtype=np.int64)
    rows, cols = np.nonzero(Mul == 0)  # identity is index 0
    inv[rows] = cols
    return G, Mul, inv


def _nbr(G, Mul, inv, S):
    """Neighbour array (2G x d): rows 0..G-1 are A-vertices, rows G..2G-1 are B-vertices."""
    Sa = np.asarray(S, dtype=np.int64)
    Si = inv[Sa]
    return np.vstack([G + Mul[:, Sa], Mul[:, Si]])


def _unreached(nbr, N, D, srcs):
    """Total number of vertices not reached within D steps, summed over the source vertices."""
    total = 0
    for src in srcs:
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nxt = nbr[frontier].ravel()
            nxt = np.unique(nxt[~seen[nxt]])
            if nxt.size == 0:
                break
            seen[nxt] = True
            frontier = nxt
        total += N - int(seen.sum())
    return total


def _search(G, Mul, inv, d, D, rng, deadline, iters):
    """Hill-climb / anneal over S (with identity fixed in S). Returns S with zero defects, or None."""
    N = 2 * G
    S = [0] + rng.sample(range(1, G), d - 1)
    cost = _unreached(_nbr(G, Mul, inv, S), N, D, (0, G))
    if cost == 0:
        return S
    for t in range(iters):
        if time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        new = rng.randrange(1, G)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _unreached(_nbr(G, Mul, inv, S), N, D, (0, G))
        temp = max(0.3, 3.0 * (1.0 - t / iters))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            if cost == 0:
                return S
        else:
            S[i] = old
    return None


def _edges(G, Mul, S):
    """Edge list of the bi-Cayley graph for the given S (degree len(S), all edges distinct)."""
    Sa = np.asarray(S, dtype=np.int64)
    A = np.repeat(np.arange(G, dtype=np.int64), len(S))
    B = (G + Mul[:, Sa]).ravel()
    return list(zip(A.tolist(), B.tolist()))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []

    if D == 2 or d <= 2:
        return best_n, best_e

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None and pg[0] > best_n and lib.is_valid(pg[0], pg[1], d, D):
            best_n, best_e = pg
            if lib.is_prime_power(d - 1):
                return best_n, best_e

    rng = random.Random(seed)
    best_G = best_n // 2  # start from the order of the fallback

    while time.monotonic() < deadline:
        step = rng.randint(1, max(2, best_G // 60))
        target = best_G + step
        m, k, r = _sample_group(target, rng)
        G, Mul, inv = _group(m, k, r)
        if G <= best_G:
            continue
        attempt_deadline = min(deadline, time.monotonic() + max(0.5, 0.05 * budget))
        S = _search(G, Mul, inv, d, D, rng, attempt_deadline, 4000)
        if S is None:
            continue
        n = 2 * G
        e = _edges(G, Mul, S)
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
            best_G = G

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
