"""Bipartite degree-diameter search for the d=10, D=5 target, using Haar graphs over metacyclic groups.

CONSTRUCTION.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A) and
(g, B) for g in G, with edges (g, A) ~ (s*g, B) for s in S.  It is bipartite and d-regular with 2|G|
vertices.  Its diameter is at most 5 exactly when (S^-1 S)^2 = G and (S S^-1)^2 = G.

SEARCH.  For a nonabelian group of order just above 2000 (so the graph beats the record of 4000), simulated
annealing changes one element of S at a time.  The cost is the number of group elements not covered by
the two squared sets.  A cost of 0 gives a valid graph, which is confirmed with lib.is_valid.  Several
groups are tried in turn, each with a time slice.

SAFETY.  A valid smaller Haar fallback (order 3582) is verified first and returned if the search fails.
Other (d, D) cases return a small always-valid graph.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- groups

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def group_candidates(lo, hi):
    """Nonabelian (m, k, lam) with lo <= m*k <= hi, ordered by increasing order."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, 40):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lam = next((l for l in range(2, m)
                        if math.gcd(l, m) == 1 and pow(l, k, m) == 1 % m), None)
            if lam is not None:
                out.append((m, k, lam))
    return out


# ----------------------------------------------------------------------------- Haar graphs

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------- annealing

def _cover_count(MT, N, X):
    """Number of distinct products x*y over x, y in the set X (given as an index array)."""
    Xu = np.unique(X)
    P = MT[np.ix_(Xu, Xu)].ravel()
    mark = np.zeros(N, dtype=bool)
    mark[P] = True
    return int(mark.sum())


def cost(MT, inv, S):
    """Uncovered elements in (S^-1 S)^2 and (S S^-1)^2.  Zero means the Haar graph has diameter <= 5."""
    N = MT.shape[0]
    Si = inv[S]
    T = MT[Si][:, S].ravel()    # S^-1 S
    U = MT[S][:, Si].ravel()    # S S^-1
    return (N - _cover_count(MT, N, T)) + (N - _cover_count(MT, N, U))


def anneal(MT, inv, d, deadline, rng, T=1.5):
    """Simulated annealing over d-subsets S.  Returns (best_cost, best_S)."""
    N = MT.shape[0]
    S = rng.choice(N, size=d, replace=False).astype(np.int64)
    cur = cost(MT, inv, S)
    best_c, best_S = cur, S.copy()
    while cur > 0 and time.monotonic() < deadline:
        i = int(rng.integers(d))
        x = int(rng.integers(N))
        if x in S:
            continue
        S2 = S.copy()
        S2[i] = x
        c = cost(MT, inv, S2)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            S, cur = S2, c
            if cur < best_c:
                best_c, best_S = cur, S.copy()
    return best_c, best_S


# ------------------------------------------------------------------------------------- entry point

TARGET = (10, 5)

# Valid smaller Haar graph (order 3582), checked at run time; baseline if the search fails.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    deadline = t0 + max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None

    cands = group_candidates(2001, 2200) + group_candidates(2201, 2600)
    idx = 0
    while cands and time.monotonic() + 2.0 < deadline:
        m, k, lam = cands[idx % len(cands)]
        idx += 1
        try:
            MT, inv = group_meta(m, k, lam)
        except Exception:
            continue
        slice_end = min(deadline, time.monotonic() + 12.0)
        c, S = anneal(MT, inv, d, slice_end, rng)
        if c == 0:
            res = checked(MT, S, d, D)
            if res is not None and (best is None or res[0] > best[0]):
                return res

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
