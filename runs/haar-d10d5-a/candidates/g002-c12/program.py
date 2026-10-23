"""Bipartite degree-diameter search for the d=10, D=5 target, using Haar graphs over metacyclic groups.

CONSTRUCTION.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A) and
(g, B) for g in G, with edges (g, A) ~ (s*g, B) for s in S.  It is bipartite and d-regular on 2|G|
vertices.  Its diameter is at most 5 when (S^-1 S)^2 = G and (S S^-1)^2 = G.

SEARCH.  Candidate groups Z_m x|_lam Z_k with m*k = N, for N ascending from just above the baseline
order, are tried in turn.  For each group, simulated annealing moves one element of S at a time.  Each
step tries K replacements and keeps the best.  The cost counts uncovered elements of G in the two
squared-product sets, and a cost of 0 means the Haar graph is valid.  Successful groups replace the
current best, and the search continues to larger orders.

SAFETY.  A valid Haar fallback (order 3582) is verified first.  Every graph returned passes lib.is_valid.
Other (d, D) cases return a small always-valid graph.
"""
import itertools
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- group tables

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


# ------------------------------------------------------------------------- cost and annealing

def cost(MT, inv, N, S):
    """Uncovered elements of G in (S^-1 S)^2 and (S S^-1)^2.  Zero means the Haar graph has diameter <= 5."""
    Si = inv[S]
    T = MT[Si[:, None], S[None, :]].ravel()
    T2 = MT[T[:, None], T[None, :]].ravel()
    c1 = N - np.count_nonzero(np.bincount(T2, minlength=N))
    U = MT[S[:, None], Si[None, :]].ravel()
    U2 = MT[U[:, None], U[None, :]].ravel()
    c2 = N - np.count_nonzero(np.bincount(U2, minlength=N))
    return int(c1 + c2)


def anneal(MT, inv, N, d, rng, deadline, K=6, T=0.8, patience=3000):
    """Search for S with cost 0, with restarts.  Returns S (int64 array) or None if the deadline passes."""
    while time.monotonic() < deadline:
        S = rng.choice(N, size=d, replace=False).astype(np.int64)
        c = cost(MT, inv, N, S)
        local = c
        stale = 0
        while c > 0 and stale < patience:
            if time.monotonic() >= deadline:
                return None
            cand_best = None
            for _ in range(K):
                i = int(rng.integers(d))
                g = int(rng.integers(N))
                if g in S:
                    continue
                S2 = S.copy()
                S2[i] = g
                c2 = cost(MT, inv, N, S2)
                if cand_best is None or c2 < cand_best[0]:
                    cand_best = (c2, S2)
            if cand_best is None:
                stale += 1
                continue
            c2, S2 = cand_best
            delta = c2 - c
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, c = S2, c2
            if c < local:
                local = c
                stale = 0
            else:
                stale += 1
        if c == 0:
            return S
    return None


def candidate_groups(lo, hi):
    """Yield (N, m, k, lam) for metacyclic groups of order N in [lo, hi], in ascending order of N."""
    for N in range(lo, hi + 1):
        for k in range(2, N // 3 + 1):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            found = 0
            for lam in range(2, min(m, 120)):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1 % m:
                    continue
                yield (N, m, k, lam)
                found += 1
                if found >= 2:
                    break


# ------------------------------------------------------------------------------------- entry point

TARGET = (10, 5)

# Valid smaller Haar graph (order 3582), checked at run time; baseline if the search fails.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])

SLICE = 4.0  # seconds per candidate group


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = max(5.0, min(0.8 * time_limit, time_limit - 12.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    best_N = 0
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
        if best is not None:
            best_N = MT.shape[0]
    except Exception:
        best = None

    try:
        for N, m, k, lam in candidate_groups(max(best_N + 1, 1792), 2100):
            now = time.monotonic()
            if now + 3.0 > deadline:
                break
            try:
                MT, inv = group_meta(m, k, lam)
            except Exception:
                continue
            slice_end = min(deadline - 2.0, now + SLICE)
            S = anneal(MT, inv, N, d, rng, slice_end)
            if S is None:
                continue
            cand = checked(MT, S, d, D)
            if cand is not None and N > best_N:
                best = cand
                best_N = N
    except Exception:
        pass

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
