"""Haar-graph search for the (d=6, D=5) target, with a verified 660-vertex fallback.

NEW IDEA (not in the parent): a single-orbit Haar construction on a group of order 343 = 7^3.
The Haar graph H(G, S) has vertices (g, A) and (g, B) for g in G, and edges (g, A) ~ (s*g, B) for s in S,
with |S| = d.  It is d-regular and bipartite with 2|G| vertices.  By the criterion
(S^-1 S)^2 = G and (S S^-1)^2 = G, the diameter is at most 5 exactly when both sets cover G.
So the search cost is the number of uncovered elements, computed with a few numpy products on a
36-element set.  For |G| = 343 the Haar graph has 686 vertices, which beats the record 684.
The parent's 4-orbit search is dropped.  Heisenberg(7) is tried first, then metacyclic groups of
orders 343..360.  Every candidate is checked with lib.is_valid, and the parent's 660-vertex Haar graph
is the fallback.
"""
import math
import time
from math import gcd

import numpy as np

import lib


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int64)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = ((a[:, None] + pw[j][:, None] * a[None, :]) % m) * k + (j[:, None] + j[None, :]) % k
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p (order p^3): (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b'), index a*p^2 + b*p + c."""
    e = np.arange(p ** 3, dtype=np.int64)
    A, B, C = e // (p * p), (e // p) % p, e % p
    Ap = (A[:, None] + A[None, :]) % p
    Bp = (B[:, None] + B[None, :]) % p
    Cp = (C[:, None] + C[None, :] + A[:, None] * B[None, :]) % p
    return _finish(Ap * p * p + Bp * p + Cp)


def candidates(lo, hi):
    """Groups of order near the target: Heis(7) (order 343) first, then metacyclic groups of order lo..hi."""
    out = [(343, lambda: group_heis(7))]
    for M in range(lo, hi + 1):
        for m in range(2, M):
            if M % m:
                continue
            k = M // m
            if k < 2:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((M, lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
                    break
    out.sort(key=lambda t: t[0])  # stable: Heis(7) stays first among order 343
    return out[:16]


# ------------------------------------------------------------------------ Haar search

def haar_cost(MT, inv, M, S):
    """Uncovered group elements: 2M - |(S^-1 S)^2| - |(S S^-1)^2|.  Zero means the Haar graph has diameter <= 5."""
    Si = inv[S]
    X1 = np.unique(MT[Si[:, None], S[None, :]])
    U1 = np.unique(MT[X1[:, None], X1[None, :]])
    X2 = np.unique(MT[S[:, None], Si[None, :]])
    U2 = np.unique(MT[X2[:, None], X2[None, :]])
    return 2 * M - U1.size - U2.size


def haar_edges(MT, M, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex h is M + h; (g, A) ~ (s*g, B) for s in S."""
    edges = []
    for s in S:
        for g in range(M):
            edges.append((g, M + int(MT[int(s), g])))
    return 2 * M, edges


def anneal(MT, inv, M, d, D, deadline, rng):
    """Annealing over S (|S| = d) with random restarts.  Returns a (n, edges) that passes lib.is_valid, or None."""
    while time.monotonic() < deadline:
        S = rng.choice(M, d, replace=False).astype(np.int64)
        cur = haar_cost(MT, inv, M, S)
        T = 1.2
        since = 0
        while since < 3000 and time.monotonic() < deadline:
            if cur == 0:
                n, edges = haar_edges(MT, M, S)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
                break  # cost said 0 but the check disagrees: restart
            i = int(rng.integers(d))
            x = int(rng.integers(M))
            if np.any(S == x):
                since += 1
                continue
            S2 = S.copy()
            S2[i] = x
            c2 = haar_cost(MT, inv, M, S2)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S = S2
                cur = c2
                since = 0 if delta < 0 else since + 1
            else:
                since += 1
    return None


# ------------------------------------------------------------------------ fallback

FALLBACK_S = [0, 179, 116, 180, 47, 306]


def haar_fallback():
    """Valid 660-vertex Haar graph (group_meta(33, 10, 26))."""
    MT, _ = group_meta(33, 10, 26)
    N = MT.shape[0]
    edges = []
    for s in FALLBACK_S:
        for g in range(N):
            edges.append((g, N + int(MT[s, g])))
    return 2 * N, edges


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    try:
        if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
            n, e = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, e, d, D):
                return n, e
        n, e = lib.haar_graph(d, range(d))
        if lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return 2, [(0, 1)]


# ------------------------------------------------------------------------ entry point

TARGET = (6, 5)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(1.0, min(0.80 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = candidates(343, 360)
    best = None
    for idx, (M, builder) in enumerate(cands):
        if best is not None and best[0] >= 2 * M:
            continue
        now = time.monotonic()
        rem = deadline - now
        if rem <= 0.5:
            break
        if idx == 0:
            end = now + rem * 0.35
        else:
            end = now + rem / (len(cands) - idx)
        try:
            MT, inv = builder()
            if MT.shape[0] != M:
                continue
            res = anneal(MT, inv, M, d, D, end, rng)
            if res is not None and (best is None or res[0] > best[0]):
                best = res
        except Exception:
            continue
    if best is not None:
        return best
    try:
        n, edges = haar_fallback()
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
