"""Haar-graph programs for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a connection set S of d elements, the Haar graph has vertices (g, A) and
(g, B) for g in G, with edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, has 2|G| vertices,
and has diameter at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements
on both sides; cost 0 means valid.

THIS VERSION.  The new idea is an ORDER LADDER.  Instead of spending the budget on a few fixed large groups
(which the parent never closed), we start from the best valid fallback (order N0, 2*N0 vertices) and only
try nonabelian metacyclic groups Z_m x|_lam Z_k whose order is strictly larger than N0.  Candidates are
tried in ascending order of group order with a short, adaptive search slice.  Every success is checked with
lib.is_valid, becomes the new incumbent, and removes all candidates that no longer beat it.  So the returned
graph is monotonically improving and always valid, even when the top orders fail.

NEW HELPERS.  meta_candidates() enumerates (m, k, lam) triples with m prime, gcd(k, m-1) > 1 (so a
nontrivial lam with lam^k = 1 mod m exists, which makes the group nonabelian), and order in a given range.
"""
import itertools
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


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Annealing over d-subsets of the group, with restarts from random sets.
    Returns (best S, best cost); cost 0 means valid."""
    N = MT.shape[0]
    S0 = None if S0 is None else np.array(S0, dtype=np.int32)
    best, bestc = None, 10 ** 9
    S, cur, since = S0.copy() if S0 is not None else None, None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    if S0 is not None:
        c0 = cost(MT, inv, S0)
        best, bestc = S0.copy(), c0
        if c0 == 0:
            return best, 0
    while time.monotonic() < deadline:
        if S is None:
            if S0 is not None and rng.random() < 0.5:
                S = S0.copy()
                for i in rng.choice(d, 2, replace=False):
                    S[i] = rng.integers(N)
                if len(set(S.tolist())) < d:
                    S = random_set()
            else:
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


# ============================================================================ NEW: order ladder helpers

def _primes_upto(n):
    """All primes <= n (simple sieve)."""
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n + 1) if s[i]]


def meta_candidates(lo, hi):
    """Nonabelian metacyclic candidates Z_m x|_lam Z_k with lo <= m*k <= hi.

    m is prime, and gcd(k, m-1) > 1 so a nontrivial lam (lam != 1, lam^k = 1 mod m) exists.
    Returns [(order, m, k, lam)] sorted by ascending order, then by larger gcd (richer action first).
    """
    out = []
    for m in _primes_upto(hi):
        if m < 5:
            continue
        for k in range(max(2, -(-lo // m)), hi // m + 1):
            g = math.gcd(k, m - 1)
            if g == 1:
                continue
            lam = next((l for l in range(2, m) if pow(l, k, m) == 1), None)
            if lam is None:
                continue
            out.append((m * k, g, m, k, lam))
    out.sort(key=lambda t: (t[0], -t[1]))
    return [(N, m, k, lam) for N, _, m, k, lam in out]


def ladder(d, D, seed, time_limit, fallback, max_order):
    """Start from the valid fallback and climb: try candidate groups of strictly larger order,
    keep every checked success as the new incumbent, and prune candidates that no longer beat it."""
    t0 = time.monotonic()
    end_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)

    best, best_n = None, 0
    try:
        MT, _ = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            best, best_n = g, g[0]
    except Exception:
        pass

    cands = [c for c in meta_candidates(best_n // 2 + 1, max_order) if 2 * c[0] > best_n]
    while cands and time.monotonic() < end_all:
        remaining = end_all - time.monotonic()
        slice_s = max(2.0, 0.15 * remaining)
        N, m, k, lam = cands.pop(0)
        try:
            MT, inv = group_meta(m, k, lam)
            S, c = search(MT, inv, d, None, min(end_all, time.monotonic() + slice_s), rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None and g[0] > best_n:
                best, best_n = g, g[0]
                cands = [x for x in cands if 2 * x[0] > best_n]

    return best if best is not None else trivial(d, D)


# ======================================================================================== cell: d10D5
TARGET = (10, 5)
MAX_ORDER = 2100   # largest group order tried (vertices = 2 * order)

# Valid smaller Haar graph (order 1791, 3582 vertices), checked at run time; the ladder climbs from it.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        return ladder(d, D, seed, time_limit, FALLBACK, MAX_ORDER)
    except Exception:
        return trivial(d, D)
