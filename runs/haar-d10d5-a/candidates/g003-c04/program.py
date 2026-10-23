"""Bipartite degree-diameter search for the d=10, D=5 target, using Haar graphs over non-abelian groups.

CONSTRUCTION.  For a finite group G and a connection set S of d elements, the Haar graph has vertices
(g, A) and (g, B) for g in G, with edges (g, A) ~ (s*g, B) for s in S. It is bipartite and d-regular
on 2|G| vertices. Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G. So the cost of S is
the number of uncovered group elements in those two squared sets, and S is valid exactly when the cost is 0.

SEARCH.  Groups are metacyclic Z_m x| Z_k (non-abelian, one per order N in 1792..2000). The side group
order is bisected over these orders. Each probe runs simulated annealing on S (with the identity fixed
in S, which is WLOG by relabelling), using full cost recomputation with numpy and random restarts when
stuck. The largest order with a zero-cost S wins. Every result passes lib.is_valid inside checked().

SAFETY.  A valid smaller Haar graph (order 3582) is verified first and kept as the baseline. Only graphs
that pass lib.is_valid are returned. Other (d, D) cases return a small always-valid graph.
"""
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


# ------------------------------------------------------------------------- annealing over S

def _cost(MT, inv, S, N):
    """Uncovered elements of (S^-1 S)^2 plus uncovered elements of (S S^-1)^2."""
    iS = inv[S]
    total = 0
    for X, Y in ((iS, S), (S, iS)):
        P = MT[X[:, None], Y[None, :]].ravel()
        Q = MT[P[:, None], P[None, :]].ravel()
        mark = np.zeros(N, dtype=bool)
        mark[Q] = True
        total += N - int(np.count_nonzero(mark))
    return total


def _anneal(MT, inv, N, d, deadline, rng):
    """Anneal S (containing the identity 0) until cost 0 or the deadline. Returns S as a list, or None."""
    while time.monotonic() < deadline:
        S = np.empty(d, dtype=np.int64)
        S[0] = 0
        S[1:] = rng.choice(np.arange(1, N), size=d - 1, replace=False)
        cur = _cost(MT, inv, S, N)
        best = cur
        stale = 0
        T = float(rng.uniform(0.5, 2.0))
        while cur > 0 and stale < 4000:
            if time.monotonic() >= deadline:
                break
            i = int(rng.integers(1, d))
            e = int(rng.integers(1, N))
            if e in S:
                continue
            old = int(S[i])
            S[i] = e
            new = _cost(MT, inv, S, N)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                S[i] = old
            if cur < best:
                best = cur
                stale = 0
            else:
                stale += 1
        if cur == 0:
            return [int(x) for x in S]
    return None


def _groups(lo, hi):
    """One non-abelian Z_m x| Z_k for each order N in (lo, hi], as (N, m, k, lam) tuples."""
    out = []
    for N in range(lo + 1, hi + 1):
        found = None
        for k in range(3, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                break
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    found = (N, m, k, lam)
                    break
            if found:
                break
        if found:
            out.append(found)
    return out


# ------------------------------------------------------------------------------------- entry point

TARGET = (10, 5)
FALLBACK_N = 1791  # order of the fallback group Z_199 x| Z_9

# Valid smaller Haar graph (order 3582), checked at run time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = max(2.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None

    try:
        cands = _groups(FALLBACK_N, 2000)
        lo, hi = 0, len(cands)
        slice_t = max(3.0, budget / 6.0)
        while lo < hi and time.monotonic() + 2.0 < deadline:
            mid = (lo + hi) // 2
            N, m, k, lam = cands[mid]
            MT, inv = group_meta(m, k, lam)
            until = min(deadline, time.monotonic() + slice_t)
            S = _anneal(MT, inv, N, d, until, rng)
            res = checked(MT, S, d, D) if S is not None else None
            if res is not None:
                best = res
                lo = mid + 1
            else:
                hi = mid
    except Exception:
        pass

    if best is not None:
        return best
    return trivial(d, D)
