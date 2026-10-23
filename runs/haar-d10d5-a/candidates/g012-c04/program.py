"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

Haar graph over a group G with connection set S (|S| = d): vertices (g, A), (g, B) for g in G, and edges
(g, A) ~ (s*g, B) for s in S. It is bipartite, d-regular, has 2|G| vertices, and its diameter is at most 5
iff (S^-1 S)^2 = G and (S S^-1)^2 = G. A cost-0 set S gives a valid graph, which is checked with lib.is_valid
before it is returned.

This version changes the group family. The parent only used metacyclic groups Z_m x| Z_k. Here most of the
time goes to small non-abelian groups whose order is just above 2000 (SL(2,7) x Z_6, SL(2,5) x Z_17,
Heis(7) x Z_6, AGL(1,47), SL(2,13), Heis(13)). Any valid group of order >= 2001 beats the record of 4000.
Metacyclic groups of order 1792..2000 are interleaved as a safety net, so a 3584-level result is still
reachable. If nothing checks out, a precomputed valid smaller Haar graph is returned, and for other (d, D)
a trivial always-valid graph is returned.
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
    """Heisenberg group mod p, order p^3, identity (0,0,0) first."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, order p(p^2-1), identity first."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p,
                         (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q):
    """AGL(1, q) = GF(q) x| GF(q)^*, order q(q-1), identity first. q a prime power."""
    F = lib.GF(q)
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in range(1, q) if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    N = n0 * k
    c = np.arange(k, dtype=np.int64)
    cc = (c[:, None] + c[None, :]) % k          # cc[c1, c2] = (c1 + c2) mod k
    MT = np.empty((N, N), dtype=np.int32)
    for g in range(n0):
        arr = MT0[g][None, :, None].astype(np.int64) * k + cc[:, None, :]   # (k, n0, k)
        MT[g * k:(g + 1) * k] = arr.reshape(k, N)
    return _finish(MT)


def make_group(key):
    """Build a group from a key tuple; returns (MT, inv)."""
    kind = key[0]
    if kind == "sl2x":
        return group_times_cyclic(group_sl2(key[1]), key[2])
    if kind == "heisx":
        return group_times_cyclic(group_heis(key[1]), key[2])
    if kind == "sl2":
        return group_sl2(key[1])
    if kind == "heis":
        return group_heis(key[1])
    if kind == "agl":
        return group_agl(key[1])
    raise ValueError(key)


# ------------------------------------------------------------------------------------------------ search

def _cover(MT, N, P):
    """Boolean array of the elements covered by products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """(side-0 products S_i^-1 S_j, side-1 products S_i S_j^-1) as flat arrays."""
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
    xi = inv[X]
    for side in (0, 1):
        F = np.unique(MT[ri[:, None], rest[None, :]] if side == 0 else MT[rest[:, None], ri[None, :]])
        base = _cover(MT, N, F)
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
    """Simulated-annealing style local search over d-subsets containing 0. Returns (best S, best cost)."""
    N = MT.shape[0]

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    S = random_set()
    cur = cost(MT, inv, S)
    best, bestc = S.copy(), cur
    if cur == 0:
        return best, 0
    since = 0
    while time.monotonic() < deadline:
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
            S = random_set()
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = S.copy(), cur
                if cur == 0:
                    return best, 0
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


# ======================================================================================== target d10D5
TARGET = (10, 5)

# Special non-abelian groups with order just above 2000 (any valid one beats the record 4000).
SPECIAL = [
    ("sl2x", 7, 6),    # 336 * 6 = 2016
    ("sl2x", 5, 17),   # 120 * 17 = 2040
    ("heisx", 7, 6),   # 343 * 6 = 2058
    ("agl", 47),       # 47 * 46 = 2162
    ("sl2", 13),       # 2184
    ("heis", 13),      # 2197
]

SLICE = 5.0           # seconds of annealing per candidate group
LO_META, HI_META = 1792, 2000   # metacyclic safety net (valid order 1792 already beats 3584)

FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def metacyclic_candidates(lo, hi):
    """All (N, m, k, lam) with N = m*k in [lo, hi], k >= 2, m >= 3, and lam a non-trivial unit with lam^k = 1 mod m."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1:
                    continue
                out.append((N, m, k, lam))
    return out


def run_search(d, D, seed, time_limit):
    """Interleave special non-abelian groups (2 of every 3 slices) with metacyclic safety-net groups.
    Returns the first checked valid Haar graph, else the fallback, else a trivial graph."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.85 * time_limit
    rng = np.random.default_rng(seed)

    keyed = {}
    for c in metacyclic_candidates(LO_META, HI_META):
        keyed.setdefault(c[0], []).append(c)
    meta_order = []
    for N in sorted(keyed):
        grp = keyed[N]
        rng.shuffle(grp)
        meta_order.extend(grp)

    cache = {}
    si = 0
    mi = 0
    it = 0
    while True:
        now = time.monotonic()
        remaining = deadline_all - now
        if remaining < 1.0:
            break
        slice_end = now + min(SLICE, remaining)
        try:
            if it % 3 != 2 and SPECIAL:
                key = SPECIAL[si % len(SPECIAL)]
                si += 1
                if key not in cache:
                    cache[key] = make_group(key)
                MT, inv = cache[key]
            elif meta_order:
                _, m, k, lam = meta_order[mi % len(meta_order)]
                mi += 1
                MT, inv = group_meta(m, k, lam)
            else:
                break
            S, c = search(MT, inv, d, slice_end, rng)
        except Exception:
            it += 1
            continue
        it += 1
        if c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g

    try:
        MT, inv = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run_search(d, D, seed, time_limit)
