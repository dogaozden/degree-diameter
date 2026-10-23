"""Bipartite degree-diameter search for the d=10, D=5 target, using Haar graphs over metacyclic groups.

CONSTRUCTION.  For a finite group G and a 10-element set S in G, the Haar graph has vertices (g, A) and
(g, B) for g in G, with edges (g, A) ~ (s*g, B) for s in S. It is bipartite and 10-regular with 2|G|
vertices. Its diameter is at most 5 exactly when (S^-1 S)^2 = G and (S S^-1)^2 = G.

SEARCH.  For each candidate non-abelian group Z_m x|_lam Z_k with order N = m*k just above 2000 (so the
graph beats the record 4000), simulated annealing moves one element of S at a time. The cost counts the
elements missing from (S^-1 S)^2 and (S S^-1)^2. The annealer restarts when it stalls. A cost of 0 is
verified with lib.is_valid before it is returned.

SAFETY.  A valid smaller Haar fallback (order 3582) is verified first and kept unless a larger verified
graph is found. Other (d, D) cases return a small always-valid graph.
"""
import itertools
import math
import time
from math import gcd

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


# ------------------------------------------------------------------- annealing over S

def cost(S, MT, inv, N):
    """Number of group elements missing from (S^-1 S)^2 plus those missing from (S S^-1)^2."""
    Si = inv[S]
    W1 = MT[Si[:, None], S[None, :]].ravel()   # s^-1 t
    W2 = MT[S[:, None], Si[None, :]].ravel()   # s t^-1
    total = 0
    for W in (W1, W2):
        P = MT[W[:, None], W[None, :]].ravel()
        total += N - int(np.count_nonzero(np.bincount(P, minlength=N)))
    return total


def anneal(MT, inv, N, d, rng, until):
    """Anneal a connection set S of size d until its cost is 0 (return S) or time runs out (return None)."""
    T = 0.6
    while time.monotonic() < until:
        S = rng.choice(N, size=d, replace=False).astype(np.int64)
        c = cost(S, MT, inv, N)
        best = c
        stale = 0
        while True:
            if c == 0:
                return S
            if time.monotonic() >= until:
                return None
            if stale > 3000:
                break
            i = int(rng.integers(d))
            x = int(rng.integers(N))
            if np.any(S == x):
                continue
            S2 = S.copy()
            S2[i] = x
            c2 = cost(S2, MT, inv, N)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                S, c = S2, c2
            if c < best:
                best = c
                stale = 0
            else:
                stale += 1
    return None


def candidate_groups(lo, hi):
    """Yield (N, m, k, lam) for non-abelian Z_m x|_lam Z_k with N = m*k in [lo, hi], in ascending N."""
    for N in range(lo, hi + 1):
        for k in range(2, 61):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            for lam in range(2, m):
                if gcd(lam, m) != 1 or lam % m == 1:
                    continue
                if pow(lam, k, m) != 1 % m:
                    continue
                yield N, m, k, lam


def search(d, D, deadline, rng, slice_s=6.0):
    """Round-robin over candidate groups, annealing each for a time slice. Returns a verified (n, edges) or None."""
    for N, m, k, lam in candidate_groups(2001, 2400):
        now = time.monotonic()
        if now + 1.0 >= deadline:
            break
        try:
            MT, inv = group_meta(m, k, lam)
        except Exception:
            continue
        S = anneal(MT, inv, N, d, rng, min(deadline, now + slice_s))
        if S is not None:
            res = checked(MT, S, d, D)
            if res is not None:
                return res
    return None


# ------------------------------------------------------------------------------------- entry point

TARGET = (10, 5)

# Valid smaller Haar graph (order 3582), checked at run time; baseline if the search fails.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None

    try:
        found = search(d, D, deadline, rng)
        if found is not None and (best is None or found[0] > best[0]):
            best = found
    except Exception:
        pass

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
