"""Haar-graph search with a metacyclic-group frontier for the bipartite degree-diameter problem (numpy only).

Haar graph of a group G and a d-set S: vertices (g, A) and (g, B), edges (g, A) ~ (s*g, B).  It is d-regular
and bipartite with 2|G| vertices, and its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.

NEW IN THIS VERSION: instead of a fixed short list of groups, enumerate every metacyclic group
Z_m x|_lam Z_k whose order N = m*k lies in a window just above the fallback order.  Candidates are tried in
ascending order of N, each with a short annealing slice.  Once a valid graph of order N* is found, only
groups with order above N* are tried, so the search climbs the frontier.  The fallback is kept as a safety net.
Every returned graph is checked with lib.is_valid.
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


# ------------------------------------------------------- NEW: metacyclic frontier enumeration

def _powmod_vec(base, e, m):
    """Vectorised base**e mod m for an int64 array of bases."""
    res = np.ones_like(base)
    b = base % m
    while e:
        if e & 1:
            res = (res * b) % m
        b = (b * b) % m
        e >>= 1
    return res


def metacyclic_candidates(lo, hi, kmax=10, per_k=2):
    """All (N, m, k, lam) with lo <= N = m*k <= hi, 2 <= k <= kmax, and lam a unit mod m with lam^k = 1 mod m,
    lam >= 2 (non-abelian when lam != 1).  Returned in ascending order of N, then k."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, kmax + 1):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lams = np.arange(2, m, dtype=np.int64)
            lams = lams[np.gcd(lams, m) == 1]
            if len(lams) == 0:
                continue
            good = lams[_powmod_vec(lams, k, m) == (1 % m)]
            for lam in good[:per_k]:
                out.append((N, m, k, int(lam)))
    return out


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


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Simulated-annealing style local search over d-subsets of the group, with restarts when stuck.
    Returns (best S, best cost); cost 0 means a valid Haar graph."""
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
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ======================================================================================== cell: d10D5
TARGET = (10, 5)

# Valid smaller Haar graph (order 2*1791 = 3582), used when the frontier search finds nothing better.
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
FALLBACK_N = 199 * 9

LO_ORDER = 1792     # just above the fallback group order
HI_ORDER = 2060     # records are 2000 vertices-per-side; beating them needs order > 2000


def run_frontier(d, D, seed, time_limit):
    """Climb the metacyclic frontier: try groups in ascending order, keep the largest valid Haar graph."""
    t0 = time.monotonic()
    deadline = t0 + 0.75 * time_limit
    rng = np.random.default_rng(seed)

    best_graph = None
    best_N = FALLBACK_N
    cands = metacyclic_candidates(LO_ORDER, HI_ORDER)
    slice_s = 0.8

    for (N, m, k, lam) in cands:
        now = time.monotonic()
        if now >= deadline:
            break
        if N <= best_N:
            continue
        try:
            MT, inv = group_meta(m, k, lam)
            S, c = search(MT, inv, d, min(deadline, now + slice_s), rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                best_graph, best_N = g, N
    return best_graph


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    graph = None
    try:
        graph = run_frontier(d, D, seed, time_limit)
    except Exception:
        graph = None
    if graph is not None:
        return graph

    try:
        MT, _ = group_meta(*FALLBACK_GROUP)
        g = checked(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
