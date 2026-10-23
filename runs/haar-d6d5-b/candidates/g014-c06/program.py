"""Round-robin Haar-graph search for the d6 D5 target, with a valid fallback and extra group families.

Idea: a Haar graph on group G with connection set S (|S| = d) has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G.  The parent only tried four groups of order 343..360 with long
annealing runs.  This version widens the family: many metacyclic groups Z_m x| Z_k of order 343..372,
plus AGL and Heisenberg products, and gives each candidate short annealing slices in round-robin
order.  Later rounds concentrate time on candidates whose best cost is lowest.  Any cost-0 set is
built and checked with lib.is_valid.  If nothing succeeds, a precomputed valid order-330 Haar graph
is returned, and trivial() covers every other (d, D).
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


def group_agl(q, k=None):
    """GF(q) x| C_k: maps t -> a*t + b with a in the order-k subgroup of GF(q)^* (default AGL(1, q))."""
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
    """Simulated-annealing style local search over d-subsets containing the identity, from random starts.
    Returns (best S, best cost); best S is None if no evaluation fit before the deadline."""
    N = MT.shape[0]

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0
    while time.monotonic() < deadline:
        if S is None:
            S = random_set()
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


# ------------------------------------------------------------------------------------ candidate groups

TARGET = (6, 5)
FALLBACK_S = [0, 179, 116, 180, 47, 306]


def metacyclic_candidates(lo, hi):
    """(m, k, lam) with m*k in [lo, hi], lam != 1, gcd(lam, m) = 1, lam^k = 1 mod m (non-abelian metacyclic)."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1:
                    continue
                if pow(lam, k, m) != 1 % m:
                    continue
                out.append((m, k, lam))
    return out


def named_candidates():
    """Hand-picked non-metacyclic groups with order just above the threshold 342."""
    return [
        ('Heis(3)xZ13 351', lambda: group_times_cyclic(group_heis(3), 13)),
        ('Heis(7) 343', lambda: group_heis(7)),
        ('AGL(1,9)xZ5 360', lambda: group_times_cyclic(group_agl(9), 5)),
        ('AGL(1,5)xZ18 360', lambda: group_times_cyclic(group_agl(5), 18)),
        ('AGL(1,7)xZ9 378', lambda: group_times_cyclic(group_agl(7), 9)),
        ('AGL(1,8)xZ7 392', lambda: group_times_cyclic(group_agl(8), 7)),
        ('AGL(1,7;3)xZ17 357', lambda: group_times_cyclic(group_agl(7, 3), 17)),
    ]


def fallback_graph(d, D):
    """Valid order-330 Haar graph, used whenever the search finds nothing better."""
    try:
        MT, _ = group_meta(33, 10, 26)
        g = checked(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def run(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(2.0, min(0.80 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    cands = named_candidates()
    meta = metacyclic_candidates(343, 372)
    if meta:
        pick = rng.permutation(len(meta))[:60]
        for idx in pick:
            m, k, lam = meta[int(idx)]
            cands.append((f'Z{m}x|Z{k}({lam})', (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))

    stats = {}
    slice_len = 0.3
    round_no = 0
    while time.monotonic() < deadline:
        if round_no == 0:
            pick = list(range(len(cands)))
        else:
            ranked = sorted(stats, key=lambda i: stats[i])
            pick = ranked[:max(1, len(ranked) // 2)]
        if not pick:
            break
        for i in pick:
            now = time.monotonic()
            if now >= deadline:
                break
            end = min(deadline, now + slice_len)
            try:
                MT, inv = cands[i][1]()
                S, c = search(MT, inv, d, end, rng)
            except Exception:
                continue
            if S is not None:
                if c == 0:
                    g = checked(MT, S, d, D)
                    if g is not None:
                        return g
                stats[i] = min(stats.get(i, 10 ** 9), c)
        round_no += 1
        slice_len = min(8.0, slice_len * 1.5)
    return fallback_graph(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        return run(d, D, seed, time_limit)
    except Exception:
        return fallback_graph(d, D)
