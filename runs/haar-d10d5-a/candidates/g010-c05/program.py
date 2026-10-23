"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a connection set S of size d, the Haar graph has vertices (g, A), (g, B) and
edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, with 2|G| vertices.  Its diameter is at most 5
iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements on both sides; cost 0 is valid.

NEW IN THIS VERSION.
  * Candidate screening: instead of relying on one hand-picked group, enumerate many groups of order in a window
    just above the record half (2001..2080).  Candidates are metacyclic Z_m x| Z_k and direct products of those
    with Z_c (c = 2, 3).  Each candidate gets a short annealing screen, and the most promising ones are deepened.
  * Product proposals: candidate replacements for a slot mix uniform random elements with products of two current
    set elements (and inverse times element).  Products of set elements are the words that tend to cover new
    group elements, so they are often better than uniform draws.
  * Non-target fallback: a checked K_{d,d} (or edge/point) instead of an unchecked Haar graph.

Every returned graph passes lib.is_valid.  Otherwise the code falls back to a smaller checked graph.
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


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def build_params(p):
    """Build (MT, inv) for a candidate parameter tuple ('meta', m, k, lam, c)."""
    _, m, k, lam, cc = p
    base = group_meta(m, k, lam)
    return base if cc == 1 else group_times_cyclic(base, cc)


def candidate_params(lo, hi, rng):
    """Shuffled list of non-abelian candidates whose order lies in [lo, hi].  Order = c * (m*k)."""
    out = []
    for cc in (1, 2, 3):
        blo, bhi = -(-lo // cc), hi // cc
        for k in range(2, 11):
            for m in range(max(3, -(-blo // k)), bhi // k + 1):
                if not (blo <= m * k <= bhi):
                    continue
                for lam in range(2, m):
                    if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                        out.append(('meta', m, k, lam, cc))
    if not out:
        return []
    order = rng.permutation(len(out))
    return [out[i] for i in order]


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


def one_swap_scan(MT, inv, S, deadline, chunk=512):
    """Score every single-slot replacement of S.  Returns (best cost, best S)."""
    N = MT.shape[0]
    best, bestS = 10 ** 9, None
    for i in range(len(S)):
        rest = np.delete(S, i)
        for lo in range(0, N, chunk):
            if time.monotonic() >= deadline:
                return best, bestS
            X = np.arange(lo, min(N, lo + chunk), dtype=np.int32)
            X = X[~np.isin(X, rest)]
            if len(X) == 0:
                continue
            cs = batch_costs(MT, inv, S, i, X)
            j = int(np.argmin(cs))
            if cs[j] < best:
                best, bestS = int(cs[j]), S.copy()
                bestS[i] = X[j]
    return best, bestS


def propose(MT, inv, S, i, K, rng):
    """Candidate replacements for slot i: half uniform random elements, half products (or inverse-products) of set elements."""
    N = MT.shape[0]
    d = len(S)
    rest = np.delete(S, i)
    n_prod = K // 2
    rand = rng.integers(0, N, size=K - n_prod)
    p = rng.integers(0, d, size=n_prod)
    q = rng.integers(0, d, size=n_prod)
    flip = rng.random(n_prod) < 0.5
    prod = np.where(flip, MT[inv[S[p]], S[q]], MT[S[p], S[q]])
    X = np.unique(np.concatenate([rand, prod]).astype(np.int32))
    return X[~np.isin(X, rest)]


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Annealing over d-subsets of the group, with product-based proposals.
    With a start set S0, first scan its 1-swap neighbours, then anneal from it.  Restarts when stuck.
    Returns (best S or None, best cost)."""
    N = MT.shape[0]
    S0 = None if S0 is None else np.array(S0, dtype=np.int32)
    best, bestc = None, 10 ** 9
    S, cur, since = (S0.copy() if S0 is not None else None), None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    if S0 is not None:
        c0 = cost(MT, inv, S0)
        best, bestc = S0.copy(), c0
        if c0 == 0:
            return best, 0
        c1, S1 = one_swap_scan(MT, inv, S0, time.monotonic() + 0.25 * max(0.0, deadline - time.monotonic()))
        if S1 is not None and c1 < bestc:
            best, bestc, S = S1.copy(), c1, S1.copy()
            if c1 == 0:
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
        X = propose(MT, inv, S, i, K, rng)
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
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e
    if D >= 2 and d >= 1:
        e = [(i, d + j) for i in range(d) for j in range(d)]
        if lib.is_valid(2 * d, e, d, D):
            return 2 * d, e
    if D >= 1 and d >= 1:
        return 2, [(0, 1)]
    return 1, []


# ======================================================================================== target d10D5

TARGET = (10, 5)

# Near miss in Z_401 x| Z_5 (order 2005, 6 short) with its start set.
NEAR_META = ('meta', 401, 5, 39, 1)
NEAR_S0 = [0, 399, 725, 919, 893, 646, 1508, 130, 652, 957]

# Valid smaller Haar graph (order 1791, 3582 vertices), used only when nothing else reaches cost 0.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def target_search(d, D, seed, time_limit):
    """Phases: (A) the known near miss, (B) screen many candidate groups of order 2001..2080,
    (C) deepen the best pool entries.  Returns a checked graph or None."""
    t0 = time.monotonic()
    T_end = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    pool = []

    # Phase A: known near miss with its start set.
    now = time.monotonic()
    endA = now + 0.20 * (T_end - now)
    try:
        MT, inv = build_params(NEAR_META)
        S, c = search(MT, inv, d, NEAR_S0, endA, rng)
        if S is not None:
            if c == 0:
                g = checked(MT, S, d, D)
                if g is not None:
                    return g
            else:
                pool.append((c, NEAR_META, S))
        del MT, inv
    except Exception:
        pass

    # Phase B: screen candidate groups with short searches.
    now = time.monotonic()
    endB = now + 0.60 * (T_end - now)
    try:
        cands = candidate_params(2001, 2080, rng)[:400]
    except Exception:
        cands = []
    for p in cands:
        now = time.monotonic()
        if now >= endB:
            break
        try:
            MT, inv = build_params(p)
            S, c = search(MT, inv, d, None, min(endB, now + 0.7), rng)
        except Exception:
            continue
        if S is not None:
            if c == 0:
                g = checked(MT, S, d, D)
                if g is not None:
                    return g
            else:
                pool.append((c, p, S))
        del MT, inv

    # Phase C: deepen the best pool entries, splitting the remaining time.
    pool.sort(key=lambda r: r[0])
    top = pool[:3]
    for idx, (c0, p, S0) in enumerate(top):
        now = time.monotonic()
        if now >= T_end:
            break
        end = now + (T_end - now) / (len(top) - idx)
        try:
            MT, inv = build_params(p)
            S, c = search(MT, inv, d, S0, end, rng)
            if S is not None and c == 0:
                g = checked(MT, S, d, D)
                if g is not None:
                    return g
        except Exception:
            continue
    return None


def target_build(d, D, seed, time_limit):
    try:
        g = target_search(d, D, seed, time_limit)
        if g is not None:
            return g
    except Exception:
        pass
    try:
        MT, _ = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return target_build(d, D, seed, time_limit)
