"""Haar-graph search for the bipartite degree-diameter problem, diameter 5 (numpy only).

Construction: a Haar graph on a group G with connection set S (|S| = d) has 2|G| vertices, is
d-regular and bipartite, and has diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.

Changes from the parent: the search now draws on a broad pool of NON-ABELIAN groups of order
just above 1791 (the order of the valid fallback), including random metacyclic groups
Z_m x|_lam Z_k with 2 <= k <= 12, not only the named families. Each group gets a fair time
slice, and the first checked graph is returned in descending order of group order. The
fallback (order 1791, 3582 vertices) is always kept and verified with lib.is_valid, so no
case returns an invalid graph.
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


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) coordinate array (identity first) and a vectorised product."""
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
    """GF(q) x| C_k: maps t -> a*t + b with a in the order-k subgroup of GF(q)^* (default AGL(1,q))."""
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


# ------------------------------------------------------------------------------------------------ search

def _cover(MT, N, P):
    """Boolean array of elements covered by the pair products P."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X (only slot-i words are recomputed)."""
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
    """Simulated-annealing style local search over d-subsets of the group, with restarts.
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
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------- candidate families

def named_candidates():
    """Non-abelian groups with order in [1792, 2100], as (order, name, builder)."""
    return [
        (2058, 'Heis(7)xZ6', lambda: group_times_cyclic(group_heis(7), 6)),
        (2028, 'AGL(1,13)xZ13', lambda: group_times_cyclic(group_agl(13), 13)),
        (2016, 'SL(2,7)xZ6', lambda: group_times_cyclic(group_sl2(7), 6)),
        (2000, 'Heis(5)xZ16', lambda: group_times_cyclic(group_heis(5), 16)),
        (1920, 'AGL(1,16)xZ8', lambda: group_times_cyclic(group_agl(16), 8)),
        (1920, 'SL(2,5)xZ16', lambda: group_times_cyclic(group_sl2(5), 16)),
        (1890, 'AGL(1,7)xZ45', lambda: group_times_cyclic(group_agl(7), 45)),
        (1870, 'AGL(1,11)xZ17', lambda: group_times_cyclic(group_agl(11), 17)),
        (1848, 'AGL(1,8)xZ33', lambda: group_times_cyclic(group_agl(8), 33)),
        (1809, 'Heis(3)xZ67', lambda: group_times_cyclic(group_heis(3), 67)),
        (1806, 'AGL(1,43)', lambda: group_agl(43)),
        (1800, 'AGL(1,9)xZ25', lambda: group_times_cyclic(group_agl(9), 25)),
    ]


def metacyclic_candidates(rng, lo, hi):
    """One random non-trivial metacyclic group Z_m x| Z_k per (N, k), for N in [lo, hi], k in 2..12."""
    out = []
    for N in range(hi, lo - 1, -1):
        for k in range(2, 13):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            found = None
            for _ in range(200):
                lam = int(rng.integers(2, m))
                if lam != 1 and math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    found = lam
                    break
            if found is None:
                continue
            out.append((N, f'Z{m}x|{found}Z{k}',
                        (lambda m=m, k=k, lam=found: group_meta(m, k, lam))))
    return out


def build_candidates(rng, budget_count):
    """Named groups first, then a random sample of metacyclic groups, returned in descending order."""
    named = named_candidates()
    meta = metacyclic_candidates(rng, 1792, 2000)
    room = max(0, budget_count - len(named))
    if len(meta) > room:
        idx = sorted(rng.choice(len(meta), room, replace=False).tolist())
        meta = [meta[i] for i in idx]
    cands = named[:budget_count] + meta
    cands.sort(key=lambda c: -c[0])
    return cands


# ------------------------------------------------------------------------------------------- driver

FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]   # valid on group_meta(199, 9, 180), order 1791
TARGET = (10, 5)


def run(d, D, seed, time_limit):
    t0 = time.monotonic()
    end_all = t0 + min(0.8 * time_limit, max(1.0, time_limit - 8.0))
    rng = np.random.default_rng(seed)
    budget_s = end_all - t0
    cands = build_candidates(rng, max(4, int(budget_s / 3.0)))

    for idx, (N, name, builder) in enumerate(cands):
        now = time.monotonic()
        remaining = end_all - now
        if remaining < 1.0:
            break
        end = now + remaining / (len(cands) - idx)
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
        MT, _ = group_meta(199, 9, 180)
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
        return run(d, D, seed, time_limit)
    except Exception:
        try:
            MT, _ = group_meta(199, 9, 180)
            g = checked(MT, FALLBACK_S, d, D)
            if g is not None:
                return g
        except Exception:
            pass
        return trivial(d, D)
