"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

Theory: for a finite group G and a set S of d elements, the Haar graph with vertices (g,A), (g,B) and
edges (g,A)~(s*g,B) is bipartite, d-regular on 2|G| vertices, and has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G. cost(S) counts uncovered elements; cost 0 means valid.

New in this version:
  * metacyclic_plan(lo, hi, count): enumerates Z_m x| Z_k groups whose order lies in [lo, hi], nearest
    to lo first, so the search targets orders just above the record threshold (order 2000 gives 4000).
  * propose(): mixes uniform random candidates with products s_a^(+-1) * s_b of two current set
    elements. Product candidates cover the group structure more quickly than uniform ones.

Only checked graphs (lib.is_valid) are returned. A valid smaller fallback Haar graph is used otherwise.
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


# ------------------------------------------------------------------------------ new: group enumeration

def metacyclic_plan(lo, hi, count):
    """Up to `count` non-trivial metacyclic groups Z_m x|_lam Z_k with order N = m*k in [lo, hi].

    Sorted by order (smallest first), since a smaller order is more likely to admit a cost-0 set.
    Each entry is (N, m, k, lam) with lam != 1 and lam^k = 1 mod m, gcd(lam, m) = 1.
    """
    cands = []
    for N in range(lo, hi + 1):
        for k in range(2, N // 3 + 1):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            found = 0
            one = 1 % m
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != one:
                    continue
                cands.append((N, m, k, lam))
                found += 1
                if found >= 2:
                    break
    return cands[:count]


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


def propose(MT, inv, S, rng, K):
    """New: candidate replacements. Mixes uniform elements with products s_a^(+-1) * s_b of two set elements."""
    N = MT.shape[0]
    d = len(S)
    if rng.random() < 0.4:
        return rng.integers(0, N, size=K).astype(np.int32)
    a = rng.integers(d, size=K)
    b = rng.integers(d, size=K)
    left = np.where(rng.random(K) < 0.5, inv[S[a]], S[a])
    return MT[left, S[b]].astype(np.int32)


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Annealing over d-subsets of the group with restarts. Returns (best S or None, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0
    while time.monotonic() < deadline:
        if S is None:
            S = np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)
            cur = None
        if cur is None:
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = S.copy(), cur
            if cur == 0:
                return best, 0
        i = int(rng.integers(d))
        X = propose(MT, inv, S, rng, K)
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


def run(d, D, seed, time_limit, plan, fallback):
    """plan: list of (name, builder, weight); fallback: (builder, S) of a valid smaller graph."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.88 * time_limit
    rng = np.random.default_rng(seed)
    total_w = sum(w for _, _, w in plan)
    for name, builder, w in plan:
        now = time.monotonic()
        if now >= deadline_all or total_w <= 0:
            break
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g
    try:
        MT, _ = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ======================================================================================== cell: d10D5
TARGET = (10, 5)

# Valid smaller Haar graph (order 1791), checked at run time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def _target_plan():
    """Metacyclic groups with order just above 2000 (the record threshold), equal time shares."""
    plan = []
    for N, m, k, lam in metacyclic_plan(2001, 2060, 8):
        plan.append((f"Z{m} x| Z{k}, lam={lam}, order {N}",
                     lambda m=m, k=k, lam=lam: group_meta(m, k, lam), 1))
    return plan


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        plan = _target_plan()
    except Exception:
        plan = []
    return run(d, D, seed, time_limit, plan, FALLBACK)
