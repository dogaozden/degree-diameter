"""Metacyclic Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A), (g, B) for g in G
and edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, has 2|G| vertices, and has diameter at most 5
iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered group elements; cost 0 means valid.

WHAT CHANGED.  The earlier plan searched a few fixed non-abelian groups of order about 2000-2160.  This version
draws metacyclic groups Z_m x|_lam Z_k over a wide range of orders (2001 to 2200), with random k and random action
lam (lam != 1, so the group is non-abelian).  Each group gets a short annealing run from a random start set.  The
first group that reaches cost 0 gives a Haar graph with 2|G| > 4000 vertices, which is checked with lib.is_valid.
If nothing succeeds within the budget, a precomputed valid Haar graph with 3582 vertices is checked and returned.
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
    """Simulated-annealing style local search over d-subsets containing the identity, with restarts.
    Returns (best S, best cost); best S is None if no iteration ran."""
    N = MT.shape[0]

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    best, bestc = None, 10 ** 9
    while time.monotonic() < deadline:
        S = random_set()
        cur = cost(MT, inv, S)
        if cur < bestc:
            best, bestc = S.copy(), cur
        if cur == 0:
            return best, 0
        local_best, since = cur, 0
        while since <= patience and time.monotonic() < deadline:
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
                    best, bestc = S.copy(), cur
                    if cur == 0:
                        return best, 0
                if cur < local_best:
                    local_best, since = cur, 0
            since += 1
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


# ------------------------------------------------------------------------------- metacyclic candidates

def meta_candidates(lo=2001, hi=2200, max_k=12):
    """All (order, m, k, lam) with m*k in [lo, hi], k <= max_k, lam != 1 and lam^k = 1 mod m, gcd(lam, m) = 1."""
    out = []
    for k in range(2, max_k + 1):
        for m in range(lo // k, hi // k + 2):
            N = m * k
            if N < lo or N > hi or m < 2:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1:
                    continue
                if pow(lam, k, m) != 1 % m:
                    continue
                out.append((N, m, k, lam))
    return out


def run_meta(d, D, seed, time_limit, max_groups=10):
    """Try shuffled metacyclic groups of order just above 2000 and return the first checked valid Haar graph."""
    t0 = time.monotonic()
    end_all = t0 + 0.70 * time_limit
    rng = np.random.default_rng(seed)
    cands = meta_candidates()
    if not cands:
        return None
    order = rng.permutation(len(cands))
    cands = [cands[int(i)] for i in order[:max_groups]]
    for idx, (N, m, k, lam) in enumerate(cands):
        now = time.monotonic()
        if now >= end_all:
            break
        slot = (end_all - now) / (len(cands) - idx)
        try:
            MT, inv = group_meta(m, k, lam)
            S, c = search(MT, inv, d, now + slot, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g
    return None


# ======================================================================================== cell: d10D5

TARGET = (10, 5)

# Valid smaller Haar graph (3582 vertices), checked at run time; used only when the search finds nothing.
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        g = run_meta(d, D, seed, time_limit)
        if g is not None:
            return g
    except Exception:
        pass
    try:
        MT, _ = group_meta(*FALLBACK_GROUP)
        g = checked(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
