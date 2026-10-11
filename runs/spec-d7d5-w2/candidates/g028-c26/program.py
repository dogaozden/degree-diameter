import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact baseline: incidence graph of PG(2, q), diameter 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: bipartite Cayley graphs over finite groups.
#
# Group G = Z_m x| Z_k with element (a, b) coded as a*k + b and product
# (a, b)(c, e) = (a + r^b c, b + e). Given a connection set S of d distinct
# elements, the graph has A-vertices g (index g) and B-vertices h (index N+h),
# with A-vertex g adjacent to B-vertex g*s for each s in S.
#
# Left multiplication by G is an automorphism that preserves both sides, so
# the diameter is at most D iff every vertex is within distance D of a_e and
# of b_e. Degrees are exactly d and the graph is bipartite by construction.
# S is found by simulated annealing that minimises the number of unreached
# (source, vertex) pairs from the two base vertices.
# ----------------------------------------------------------------------------

def _find_r(m, k, rng):
    """Return r with gcd(r, m) = 1 and r^k = 1 mod m, or None."""
    if k == 1:
        return 1
    if m < 2:
        return None
    for _ in range(300):
        r = rng.randrange(1, m)
        if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
            return r
    return None


def _tables(m, k, r):
    """Return (N, M, invs): M[g, s] = index of g*s, invs[s] = index of s^{-1}; None if malformed."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    powers = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    M = M.astype(np.int64)
    rows, cols = np.nonzero(M == 0)
    if len(rows) != N:
        return None
    invs = np.empty(N, dtype=np.int64)
    invs[rows] = cols
    return N, M, invs


def _cost(M, invs, S, N, D):
    """Number of (base source, vertex) pairs not within distance D, for sources a_e and b_e."""
    invS = invs[S]
    total = 0
    for side in (0, 1):
        vA = np.zeros(N, dtype=bool)
        vB = np.zeros(N, dtype=bool)
        if side == 0:
            vA[0] = True
        else:
            vB[0] = True
        fA = vA.copy()
        fB = vB.copy()
        for _ in range(D):
            nB = np.zeros(N, dtype=bool)
            idx = np.flatnonzero(fA)
            if idx.size:
                nB[M[np.ix_(idx, S)].ravel()] = True
            nA = np.zeros(N, dtype=bool)
            idx = np.flatnonzero(fB)
            if idx.size:
                nA[M[np.ix_(idx, invS)].ravel()] = True
            newB = nB & ~vB
            newA = nA & ~vA
            vB |= nB
            vA |= nA
            fA, fB = newA, newB
            if not fA.any() and not fB.any():
                break
        total += 2 * N - int(vA.sum()) - int(vB.sum())
    return total


def _anneal(M, invs, N, d, D, rng, deadline, iters):
    """Search a d-subset S of G whose bipartite Cayley graph has diameter <= D. Returns S or None."""
    S = rng.sample(range(N), d)
    cost = _cost(M, invs, np.array(S, dtype=np.int64), N, D)
    inS = set(S)
    for t in range(iters):
        if cost == 0:
            break
        if (t & 63) == 0 and time.monotonic() > deadline:
            break
        p = rng.randrange(d)
        new = rng.randrange(N)
        if new in inS:
            continue
        old = S[p]
        S[p] = new
        c = _cost(M, invs, np.array(S, dtype=np.int64), N, D)
        temp = 1.5 * (1.0 - t / iters) + 0.05
        if c <= cost or rng.random() < math.exp(-(c - cost) / temp):
            cost = c
            inS.discard(old)
            inS.add(new)
        else:
            S[p] = old
    return S if cost == 0 else None


def _edges_from(N, M, S):
    """Edge list of the bipartite Cayley graph: A-vertex g is index g, B-vertex h is index N + h."""
    return [(g, N + int(M[g, s])) for g in range(N) for s in S]


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if d > 0:
        ks = [1, 2, 3, 4, 5, 6, 7, 8, 10, 12]
        while time.monotonic() < deadline - 0.5:
            try:
                T = best_n // 2 + 1 + rng.randrange(0, 6)
                k = rng.choice(ks)
                m = -(-T // k)
                if m < 1 or m * k < d:
                    continue
                r = _find_r(m, k, rng)
                if r is None:
                    continue
                tab = _tables(m, k, r)
                if tab is None:
                    continue
                N, M, invs = tab
                if 2 * N <= best_n:
                    continue
                slice_end = min(deadline, time.monotonic() + 6.0)
                S = _anneal(M, invs, N, d, D, rng, slice_end, 2500)
                if S is not None:
                    consider(2 * N, _edges_from(N, M, S))
            except Exception:
                continue

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
