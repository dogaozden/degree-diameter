"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

Construction: a Haar graph over a finite group G with a connection set S of size d has 2|G| vertices, is
d-regular and bipartite, and has diameter at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  Here the search
is over METACYCLIC groups Z_m x|_lam Z_k of orders just above the fallback (1791), with many different
(m, k, lam) choices, which is a different group family from the earlier plan.  Candidates are ordered so
that orders above 2000 (which beat the record-equivalent 4000 vertices) are tried first.

Safety: the verified fallback Haar graph (order 1791, 3582 vertices) is built and checked first, and is
returned whenever no larger graph passes lib.is_valid.  Every returned graph is checked.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------------------- group tables

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


# ------------------------------------------------------------------------------------------------ search

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j] (P an int array of pair products)."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """(side-0 pair products S_i^-1 S_j, side-1 pair products S_i S_j^-1) as flat arrays."""
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """cost of S with slot i replaced by x, for every x in the int array X (only slot-i words are recomputed)."""
    N = MT.shape[0]
    K = len(X)
    rest = np.delete(S, i)
    total = np.zeros(K, dtype=np.int64)
    offs = (np.arange(K, dtype=np.int64) * N)[:, None]
    ri = inv[rest]
    for side in (0, 1):
        F = np.unique(MT[ri[:, None], rest[None, :]] if side == 0 else MT[rest[:, None], ri[None, :]])
        base = _cover(MT, N, F)
        xi = inv[X]
        if side == 0:
            Q = np.concatenate([MT[xi[:, None], rest[None, :]], MT[ri[None, :], X[:, None]]], axis=1)
        else:
            Q = np.concatenate([MT[X[:, None], ri[None, :]], MT[rest[None, :], xi[:, None]]], axis=1)
        W = np.concatenate([MT[Q[:, :, None], F[None, None, :]].reshape(K, -1),
                            MT[F[None, None, :], Q[:, :, None]].reshape(K, -1),
                            MT[Q[:, :, None], Q[:, None, :]].reshape(K, -1)], axis=1)
        new = ~base[W]
        flat = (W + offs)[new]
        cnt = np.bincount(flat, minlength=K * N).reshape(K, N)
        total += N - int(base.sum()) - (cnt > 0).sum(axis=1)
    return total


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Simulated-annealing local search over d-subsets of the group, with random restarts.
    Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    while time.monotonic() < deadline:
        if S is None:
            S = random_set()
        if cur is None:
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = S.copy(), cur
            if cur == 0:
                return best, 0
        i = int(rng.integers(d))
        X = rng.integers(0, N, size=K).astype(np.int32)
        X = X[~np.isin(X, np.delete(S, i))]
        if len(X) == 0:
            continue
        cs = batch_costs(MT, inv, S, i, X)
        j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
        delta = int(cs[j]) - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S[i] = X[j]
            cur = int(cs[j])
            if cur < bestc:
                best, bestc, since = S.copy(), cur, 0
                if cur == 0:
                    return best, 0
            elif delta < 0:
                since = 0
        since += 1
        if since > patience:
            S, cur = None, None
    return best, bestc


# --------------------------------------------------------------------------------------------- the graph

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid (checked with lib.is_valid)."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ======================================================================================== cell: d10D5
TARGET = (10, 5)

# Verified fallback: Z_199 x| Z_9 (order 1791), giving a valid Haar graph with 3582 vertices.
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]

SLICE = 7.0   # seconds of search per metacyclic group


def candidates(rng):
    """Metacyclic groups Z_m x|_lam Z_k of order N in [2001, 2060] first, then [1792, 2000].
    Within each band the order is randomised so different groups are tried."""
    out = []
    for lo, hi in ((2001, 2060), (1792, 2000)):
        band = []
        for N in range(hi, lo - 1, -1):
            for k in range(2, N):
                if N % k:
                    continue
                m = N // k
                if m < 3:
                    continue
                lams = [lam for lam in range(2, m)
                        if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m and pow(lam, 1, m) != 1]
                if not lams:
                    continue
                pick = rng.permutation(len(lams))[:3]
                for idx in pick:
                    band.append((m, k, lams[int(idx)]))
        order = rng.permutation(len(band))
        out.extend(band[int(i)] for i in order)
    return out


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    end_all = t0 + 0.85 * time_limit
    rng = np.random.default_rng(seed)

    # Safe fallback first, so a valid answer is always in hand.
    best = None
    try:
        MT, inv = group_meta(*FALLBACK_GROUP)
        best = checked(MT, FALLBACK_S, d, D)
    except Exception:
        best = None
    if best is None:
        best = trivial(d, D)

    try:
        cands = candidates(rng)
    except Exception:
        cands = []

    for m, k, lam in cands:
        now = time.monotonic()
        if now >= end_all - 1.0:
            break
        end = min(end_all - 1.0, now + SLICE)
        try:
            MT, inv = group_meta(m, k, lam)
            S, c = search(MT, inv, d, end, rng)
            if S is not None and c == 0:
                g = checked(MT, S, d, D)
                if g is not None and g[0] > best[0]:
                    return g
        except Exception:
            continue
    return best
