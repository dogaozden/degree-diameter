"""Haar-graph seed programs for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  Let G be a finite group and S a subset of G with |S| = d.  The Haar graph has vertices (g, A) and
(g, B) for g in G, with edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, and has 2|G| vertices.
Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements on both
sides; cost 0 means valid.

NEW IN THIS VERSION.
  * Affine groups AGL(1, p) = {x -> a*x + b} of order p(p-1) join the sweep.  AGL(1,43) has order 1806 and
    AGL(1,47) has order 2162, so both lie in the search window.  Any valid order above 1792 beats the parent's
    3584 vertices.
  * The annealer gets an inverse move.  A third of the candidate replacements are inverses of current set
    elements, alongside the random and product candidates.

Only checked graphs (lib.is_valid) are returned.  If nothing is found, a precomputed valid smaller Haar graph is
returned.  Every other (d, D) gets a small always-valid graph.
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
    """Table of a group given as an (N, c) integer coordinate array (element 0 must be the identity)
    and a vectorised product mulfun(X, Y) of two (..., c) arrays."""
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
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)   # (0,0,0) is first

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, matrices (a, b, c, d), order p(p^2-1)."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_affine(p):
    """AGL(1, p) for a prime p: maps x -> a*x + b with a in 1..p-1, b in 0..p-1, order p(p-1).
    Element (a, b) has index (a-1)*p + b, so the identity (1, 0) is index 0.
    Product (a1,b1)(a2,b2) = (a1*a2, a1*b2 + b1) as composition of affine maps."""
    a = np.repeat(np.arange(1, p, dtype=np.int64), p)
    b = np.tile(np.arange(p, dtype=np.int64), p - 1)
    A1, B1 = a[:, None], b[:, None]
    A2, B2 = a[None, :], b[None, :]
    MT = (((A1 * A2) % p - 1) * p + (A1 * B2 + B1) % p).astype(np.int32)
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


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Annealing over d-subsets of the group.  Candidate replacements mix three kinds:
    random elements, products of two current set elements (product move), and inverses of current
    set elements (inverse move).  Restarts from a random set when stuck.
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
        third = K // 3
        Xr = rng.integers(0, N, size=K - 2 * third)
        pa = S[rng.integers(0, d, size=third)]
        pb = S[rng.integers(0, d, size=third)]
        Xp = MT[inv[pa], pb] if third > 0 else np.zeros(0, dtype=np.int32)
        Xi = inv[S[rng.integers(0, d, size=third)]] if third > 0 else np.zeros(0, dtype=np.int32)
        X = np.concatenate([Xr, Xp, Xi]).astype(np.int32)
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


# ======================================================================================== cell: d10D5
TARGET = (10, 5)

LO, HI = 1792, 2200   # any valid Haar graph with |G| >= 2001 beats the record 4000
SLICE = 4.0           # seconds of annealing per candidate group

FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def _is_prime(n):
    return n > 1 and all(n % q for q in range(2, int(n ** 0.5) + 1))


def metacyclic_candidates(lo, hi):
    """All (N, m, k, lam) with N = m*k in [lo, hi], k >= 2, m >= 3, lam a non-trivial unit mod m, lam^k = 1 mod m."""
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
                out.append((N, "meta", (m, k, lam)))
    return out


def special_candidates(lo, hi):
    """Non-metacyclic groups in the order range: Heisenberg mod p, SL(2, p), and AGL(1, p)."""
    out = []
    for p in (7, 11, 13):
        N = p ** 3
        if lo <= N <= hi:
            out.append((N, "heis", (p,)))
        N = p * (p * p - 1)
        if lo <= N <= hi:
            out.append((N, "sl2", (p,)))
    for p in range(3, 200):
        if not _is_prime(p):
            continue
        N = p * (p - 1)
        if lo <= N <= hi:
            out.append((N, "aff", (p,)))
    return out


def make_group(kind, args):
    """Build (MT, inv) for a candidate."""
    if kind == "meta":
        return group_meta(*args)
    if kind == "heis":
        return group_heis(*args)
    if kind == "sl2":
        return group_sl2(*args)
    if kind == "aff":
        return group_affine(*args)
    raise ValueError(kind)


def run_meta(d, D, seed, time_limit):
    """Round-robin annealing over all candidate groups of order in [LO, HI], ascending in order.
    Returns the first checked valid Haar graph, else the fallback."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.88 * time_limit
    rng = np.random.default_rng(seed)

    cands = metacyclic_candidates(LO, HI) + special_candidates(LO, HI)
    keyed = {}
    for c in cands:
        keyed.setdefault(c[0], []).append(c)
    order = []
    for N in sorted(keyed):
        grp = keyed[N]
        rng.shuffle(grp)
        order.extend(grp)

    idx = 0
    while order:
        now = time.monotonic()
        remaining = deadline_all - now
        if remaining < 0.5:
            break
        _, kind, args = order[idx % len(order)]
        idx += 1
        slice_end = now + min(SLICE, remaining)
        try:
            MT, inv = make_group(kind, args)
            S, c = search(MT, inv, d, slice_end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
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
    return run_meta(d, D, seed, time_limit)
