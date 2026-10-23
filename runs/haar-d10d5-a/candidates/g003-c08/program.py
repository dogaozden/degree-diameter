"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

A Haar graph on a group G with connection set S (|S| = d) has vertices (g, A), (g, B) and edges
(g, A) ~ (s*g, B). It is bipartite, d-regular, has 2|G| vertices, and has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G. The cost of S is the number of uncovered group elements; cost 0 is valid.

New in this version:
  * greedy_start: builds an initial S one element at a time, choosing each new element to minimise the
    uncovered count of the partial set. Restarts use it instead of uniformly random sets.
  * propose: half of the candidate replacements are products s_a * s_b of existing connection elements,
    not uniform random group elements. Products are the words that tend to cover new elements.
  * meta_candidates: metacyclic groups Z_m x|_lam Z_k of order in (1800, 2100], each with its own lam.
    They are tried from the largest order down, and the first checked valid graph is returned.

Every returned graph is checked with lib.is_valid. If no candidate succeeds, a valid smaller Haar graph is used.
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
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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
    """Boolean array of the elements covered by the products P[i]*P[j]."""
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
    """Cost of S with slot i replaced by x, for every x in the int array X (only slot-i words are recomputed)."""
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


def greedy_start(MT, inv, d, rng, K=60):
    """NEW: greedy construction of a connection set. Each step adds the sampled element that leaves the
    fewest uncovered elements in the partial set. Starts from the identity."""
    N = MT.shape[0]
    S = np.array([0], dtype=np.int32)
    while len(S) < d:
        X = np.unique(rng.integers(1, N, size=K).astype(np.int32))
        X = X[~np.isin(X, S)]
        if len(X) == 0:
            continue
        best_c, best_x = None, None
        for x in X:
            c = cost(MT, inv, np.append(S, x).astype(np.int32))
            if best_c is None or c < best_c:
                best_c, best_x = c, x
        S = np.append(S, best_x).astype(np.int32)
    return S


def propose(MT, S, rng, K):
    """NEW: candidate replacements. Half are uniform random elements, half are products of two
    existing connection elements (s_a * s_b)."""
    N = MT.shape[0]
    d = len(S)
    half = K // 2
    r = rng.integers(0, N, size=K - half)
    a = rng.integers(0, d, size=half)
    b = rng.integers(0, d, size=half)
    p = MT[S[a], S[b]]
    return np.concatenate([r, p]).astype(np.int32)


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=3000):
    """Annealing over d-subsets. Restarts use greedy_start. Returns (best S, best cost)."""
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0
    while time.monotonic() < deadline:
        if S is None:
            S = greedy_start(MT, inv, d, rng)
            cur = None
        if cur is None:
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = S.copy(), cur
            if cur == 0:
                return best, 0
        i = int(rng.integers(d))
        X = propose(MT, S, rng, K)
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

# Valid smaller Haar graph (order 1791 per side), used only when no candidate reaches cost 0.
FALLBACK_SPEC = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def meta_candidates(lo=1800, hi=2100, limit=6):
    """NEW: metacyclic groups Z_m x|_lam Z_k with m*k in (lo, hi], largest order first, two lam values each.
    Requires k >= 4 and m >= 20 so the groups are not dihedral-like."""
    out = []
    for N in range(hi, lo, -1):
        for k in range(4, N):
            if N % k:
                continue
            m = N // k
            if m < 20:
                continue
            lams = [l for l in range(2, m) if pow(l, k, m) == 1]
            for lam in lams[:2]:
                out.append((m, k, lam))
            if len(out) >= limit:
                return out[:limit]
    return out[:limit]


def run(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.8 * time_limit
    rng = np.random.default_rng(seed)
    cands = meta_candidates()
    for idx, (m, k, lam) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline - 0.5:
            break
        end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = group_meta(m, k, lam)
            S, c = search(MT, inv, d, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g
    try:
        MT, _ = group_meta(*FALLBACK_SPEC)
        g = checked(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        res = run(d, D, seed, time_limit)
    except Exception:
        res = None
    if res is None:
        return trivial(d, D)
    return res
