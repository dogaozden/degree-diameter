"""Haar-graph search with an algebraic word-covering cost for the bipartite degree-diameter problem (d=10, D=5).

NEW HELPER (not in the parent): HaarCost evaluates a connection set S in a group table directly.
For the Haar graph on G with 2|G| vertices, diameter <= 5 holds iff (S^-1 S)^2 = G and (S S^-1)^2 = G.
The cost is the number of uncovered group elements in those two sets. It is computed with 10^4 table
lookups instead of a BFS over the whole graph, which makes the search about two orders of magnitude faster.

SEARCH.  For each attempt, pick a metacyclic group Z_m x|_r Z_k of order N just above the current best
(N > 1791).  Run annealing on S with best-of-K replacements, where a move either sets a random group
element or a product/inverse-product of two elements already in S.  Restarts happen every cycle.  Any
zero-cost S is turned into a Haar graph and checked with lib.is_valid before it is accepted.
The valid parent Haar graph (3582 vertices) is the fallback, so the output is never worse than the parent's.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l).  Returns (MT, inv)."""
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    ak = idx // k
    jk = idx % k
    MT = np.empty((N, N), dtype=np.int32)
    step = 128
    for lo in range(0, N, step):
        hi = min(N, lo + step)
        a = ak[lo:hi, None]
        j = jk[lo:hi, None]
        MT[lo:hi] = ((a + pw[j] * ak[None, :]) % m) * k + (j + jk[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def metacyclic_options(N):
    """All (m, k, r) with m*k = N, k >= 2, r >= 2, gcd(r, m) = 1, r^k = 1 mod m (non-abelian choices)."""
    opts = []
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


class HaarCost:
    """Word-covering cost of a Haar-graph connection set S (a numpy array of group indices).

    cost(S) = |G \\ (S^-1 S)^2| + |G \\ (S S^-1)^2|; it is zero exactly when the Haar graph has diameter <= 5.
    """

    def __init__(self, MT, inv):
        self.MT = MT
        self.inv = inv
        self.N = MT.shape[0]

    def cost(self, S):
        MT, inv, N = self.MT, self.inv, self.N
        iS = inv[S]
        total = 0
        words = (MT[iS[:, None], S[None, :]].ravel(),   # s^-1 t
                 MT[S[:, None], iS[None, :]].ravel())   # s t^-1
        for W in words:
            W2 = MT[W[:, None], W[None, :]].ravel()
            mark = np.zeros(N, dtype=bool)
            mark[W2] = True
            total += N - int(np.count_nonzero(mark))
        return total


def haar_edges(MT, S, N):
    """Haar graph: (g, A) ~ (s*g, B) for s in S; A-vertex g is g, B-vertex g is N + g."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted(set(int(x) for x in S)):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


def anneal(hc, MT, inv, N, d, rng, deadline, cycle=2500, K=6):
    """Annealing over connection sets with restarts every `cycle` steps. Returns a zero-cost S or None."""
    while time.monotonic() < deadline:
        S = rng.choice(N, d, replace=False).astype(np.int64)
        cur = hc.cost(S)
        if cur == 0:
            return S
        for step in range(cycle):
            if (step & 63) == 0 and time.monotonic() >= deadline:
                return None
            frac = step / cycle
            temp = 0.25 + 1.5 * (1.0 - frac)
            bestc, bestS = None, None
            for _ in range(K):
                i = int(rng.integers(d))
                if rng.random() < 0.5:
                    a = int(rng.integers(d))
                    b = int(rng.integers(d))
                    if rng.random() < 0.5:
                        g = int(MT[S[a], S[b]])
                    else:
                        g = int(MT[inv[S[a]], S[b]])
                else:
                    g = int(rng.integers(N))
                if np.any(S == g):
                    continue
                S2 = S.copy()
                S2[i] = g
                c2 = hc.cost(S2)
                if bestc is None or c2 < bestc:
                    bestc, bestS = c2, S2
            if bestS is None:
                continue
            if bestc <= cur or rng.random() < math.exp(-(bestc - cur) / temp):
                S, cur = bestS, bestc
                if cur == 0:
                    return S
    return None


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(3.0, min(0.80 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        n, e = haar_edges(MT, FALLBACK_S, m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    best_N = best_n // 2 if best_n else 1791
    attempt_cap = max(4.0, 0.15 * budget)

    while time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        N = best_N + 1 + int(rng.integers(0, 12))
        try:
            opts = metacyclic_options(N)
            if not opts:
                continue
            m, k, r = opts[int(rng.integers(len(opts)))]
            MT, inv = group_table(m, k, r)
            hc = HaarCost(MT, inv)
            att_deadline = min(deadline, time.monotonic() + attempt_cap)
            S = anneal(hc, MT, inv, N, d, rng, att_deadline)
        except Exception:
            continue
        if S is None:
            continue
        try:
            n, e = haar_edges(MT, S, N)
            ok = n > best_n and lib.is_valid(n, e, d, D)
        except Exception:
            ok = False
        if ok:
            best_n, best_edges = n, e
            best_N = N

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
