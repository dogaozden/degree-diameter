"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A), (g, B) and edges
(g, A) ~ (s*g, B).  It is bipartite, d-regular, has 2|G| vertices, and has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered group elements; cost 0 means valid.

NEW IN THIS VERSION.
  * greedy_seed: builds S one element at a time, each time adding the candidate that minimises the
    uncovered count of the partial set.  It replaces random starts and gives annealing a better basin.
  * metacyclic_candidates: enumerates every metacyclic group Z_m x| Z_k with lam != 1 and order in a
    window just above 2000 (the threshold for beating 4000 vertices).  Each group gets a short greedy
    seed plus annealing, in ascending order of order, before the time goes to the named groups.
  * Every returned graph is checked with lib.is_valid.  A precomputed valid smaller graph is the fallback.
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


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) integer coordinate array (element 0 = identity) and a vectorised product."""
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sorted_codes = codes[order]
    MT = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sorted_codes, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p, order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, order p(p^2-1)."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k (default AGL(1, q)).  Product (b1, a1)(b2, a2) = (b1 + a1*b2, a1*a2)."""
    F = lib.GF(q)
    k = q - 1 if k is None else k
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    assert len(H) == k
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ---------------------------------------------------------------------------------------- cost machinery

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """(side-0 products S_i^-1 S_j, side-1 products S_i S_j^-1) as flat arrays."""
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (works for partial sets too).  Cost 0 = valid for a full set."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X (only the words involving slot i are recomputed)."""
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


# ------------------------------------------------------------------------------------- new search helpers

def greedy_seed(MT, inv, d, rng, pool=150):
    """Grow a d-set from {0}: each step adds the sampled candidate that minimises the cost of the partial set.
    Identity is always in S, which is WLOG (right translation preserves validity)."""
    N = MT.shape[0]
    T = [0]
    while len(T) < d:
        sample = rng.choice(np.arange(1, N), size=min(pool, N - 1), replace=False)
        best_c, best_x = None, None
        for x in sample:
            x = int(x)
            if x in T:
                continue
            c = cost(MT, inv, np.array(T + [x], dtype=np.int32))
            if best_c is None or c < best_c:
                best_c, best_x = c, x
        T.append(best_x)
    return np.array(T, dtype=np.int32)


def anneal(MT, inv, d, S, deadline, rng, K=24, temp=0.45, patience=2500):
    """Metropolis annealing over slot replacements, from S.  Returns (best S, best cost)."""
    N = MT.shape[0]
    S = np.array(S, dtype=np.int32)
    cur = cost(MT, inv, S)
    best, bestc = S.copy(), cur
    since = 0
    while cur > 0 and time.monotonic() < deadline:
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
        since += 1
        if since > patience:
            break
    return best, bestc


def metacyclic_candidates(lo, hi):
    """All (m, k, lam) with m*k in [lo, hi], lam != 1, lam^k = 1 mod m, gcd(lam, m) = 1 (non-abelian metacyclic)."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((m, k, lam))
    return out


# --------------------------------------------------------------------------------------------- the graph

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
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def search_group(builder, d, D, deadline, rng, slice_s):
    """Build one group, greedy-seed it, anneal for up to slice_s seconds, return a checked graph or None."""
    try:
        MT, inv = builder()
    except Exception:
        return None
    end = min(deadline, time.monotonic() + slice_s)
    S0 = greedy_seed(MT, inv, d, rng)
    S, c = anneal(MT, inv, d, S0, end, rng)
    if c == 0:
        try:
            return checked(MT, S, d, D)
        except Exception:
            return None
    return None


# ======================================================================================== cell: d10D5
TARGET = (10, 5)
WINDOW = (2001, 2100)     # group orders giving 2|G| > 4000

PLAN = [
    ('SL(2,7) x Z_6', lambda: group_times_cyclic(group_sl2(7), 6)),
    ('Heis(7) x Z_6', lambda: group_times_cyclic(group_heis(7), 6)),
    ('AGL(1,13) x Z_13', lambda: group_times_cyclic(group_agl(13), 13)),
    ('AGL(1,16) x Z_9', lambda: group_times_cyclic(group_agl(16), 9)),
]

# Valid smaller Haar graph (order 1791), checked at run time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.85 * time_limit
    rng = np.random.default_rng(seed)

    # Phase A: metacyclic scan over the window, smallest order first.
    cands = metacyclic_candidates(*WINDOW)
    cands.sort(key=lambda t: (t[0] * t[1], rng.random()))
    phaseA_end = t0 + 0.5 * (deadline - t0)
    for (m, k, lam) in cands:
        now = time.monotonic()
        if now >= phaseA_end:
            break
        g = search_group(lambda m=m, k=k, lam=lam: group_meta(m, k, lam),
                         d, D, phaseA_end, rng, slice_s=2.5)
        if g is not None:
            return g

    # Phase B: named non-metacyclic groups share the remaining time equally.
    for idx, (name, builder) in enumerate(PLAN):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(PLAN) - idx)
        g = search_group(builder, d, D, deadline, rng, slice_s=share)
        if g is not None:
            return g

    # Fallback: valid smaller Haar graph.
    try:
        MT, _ = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
