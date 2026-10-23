"""Bipartite degree-diameter search for the d=10, D=5 target, using Haar graphs over metacyclic groups.

NEW IDEA.  The parent used random bipartite regular graphs. This program searches Haar graphs
instead. Take a group G of order N and a connection set S of d elements. The Haar graph has
2N vertices, and it has diameter at most 5 exactly when both
    (S^-1 S)^2 = G   and   (S S^-1)^2 = G.
So the search minimises cost(S) = #uncovered(G, (S^-1 S)^2) + #uncovered(G, (S S^-1)^2).
Cost 0 means the graph is valid. Each cost evaluation is one vectorised numpy gather on a
precomputed multiplication table, so the annealer can afford hundreds of thousands of steps.

GROUPS.  Non-abelian metacyclic groups Z_m x|_lam Z_k (lam^k = 1 mod m, lam != 1) are tried in
increasing order of N, starting just above the current best half-order. Each candidate gets a
share of the remaining time. Every graph is still checked with lib.is_valid before it is returned.

SAFETY.  A verified Haar fallback of order 3582 is checked first. Other (d, D) cases return a
small always-valid graph.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- groups

def meta_table(m, k, lam):
    """Multiplication and inverse tables for Z_m x|_lam Z_k.

    Element (a, j) has index a*k + j, and (a, j)(b, l) = (a + lam^j b, j + l). Identity is 0.
    """
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = (((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k
                     + (j[lo:hi, None] + j[None, :]) % k)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_candidates(lo, hi, cap):
    """Yield (m, k, lam) with lo <= m*k <= hi, lam a nontrivial action, in increasing order of m*k."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            lam = next((r for r in range(2, m)
                        if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m), None)
            if lam is not None:
                out.append((m, k, lam))
                if len(out) >= cap:
                    return out
    return out


# ----------------------------------------------------------------------------- Haar graphs

def haar_edges(N, MT, S):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, and (g, A) ~ (s*g, B) for s in S."""
    edges = []
    for s in sorted({int(x) for x in S}):
        col = MT[s]
        edges.extend(zip(range(N), (N + col).astype(np.int64).tolist()))
    return 2 * N, edges


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    N = MT.shape[0]
    n, edges = haar_edges(N, MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------- annealing

def diameter_cost(MT, inv, N, S):
    """Number of group elements missed by (S^-1 S)^2 plus those missed by (S S^-1)^2."""
    Sa = np.array(S, dtype=np.int64)
    Si = inv[Sa]
    T1 = MT[Si[:, None], Sa[None, :]].ravel()          # s^-1 t
    T2 = MT[T1[:, None], T1[None, :]].ravel()          # (S^-1 S)^2
    U1 = MT[Sa[:, None], Si[None, :]].ravel()          # s t^-1
    U2 = MT[U1[:, None], U1[None, :]].ravel()          # (S S^-1)^2
    mark = np.zeros(N, dtype=bool)
    mark[T2] = True
    c1 = N - int(mark.sum())
    mark[:] = False
    mark[U2] = True
    c2 = N - int(mark.sum())
    return c1 + c2


def anneal(MT, inv, N, d, rng, deadline):
    """Random-restart Metropolis search for S with zero diameter cost. Returns S or None."""
    temp = 0.6
    while time.monotonic() < deadline:
        S = [int(x) for x in rng.choice(N, size=d, replace=False)]
        c = diameter_cost(MT, inv, N, S)
        run_best = c
        stale = 0
        while c > 0 and stale < 20000 and time.monotonic() < deadline:
            i = int(rng.integers(d))
            x = int(rng.integers(N))
            if x in S:
                continue
            S2 = S.copy()
            S2[i] = x
            c2 = diameter_cost(MT, inv, N, S2)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
                S, c = S2, c2
                if c < run_best:
                    run_best = c
                    stale = 0
                    continue
            stale += 1
        if c == 0:
            return S
    return None


# ------------------------------------------------------------------------------------- entry point

TARGET = (10, 5)

# Valid smaller Haar graph (order 3582), checked at run time.
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = meta_table(*FALLBACK_GROUP)
        best = checked(MT, FALLBACK_S, d, D)
    except Exception:
        best = None

    lo = best[0] // 2 + 1 if best is not None else 2
    cands = group_candidates(lo, lo + 400, 12)

    for idx, (m, k, lam) in enumerate(cands):
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        slice_end = time.monotonic() + remaining * 0.4
        try:
            N = m * k
            MT, inv = meta_table(m, k, lam)
            S = anneal(MT, inv, N, d, rng, slice_end)
            if S is not None:
                n, edges = haar_edges(N, MT, S)
                if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                    best = (n, edges)
        except Exception:
            pass

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
