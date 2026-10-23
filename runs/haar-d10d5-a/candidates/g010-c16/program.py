"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A), (g, B) and edges
(g, A) ~ (s*g, B).  It is bipartite, d-regular, and has 2|G| vertices.  It has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G.  cost(S) counts the uncovered elements on both sides; cost 0 means valid.

THIS VERSION (bold change).  The search moves to a different family of groups:
  * Affine-type groups V x| Z_k, with V = Z_p^2 and the generator of Z_k acting on V by a matrix M of order
    dividing k (p = 5, 7, 11).  These are non-metacyclic and were not in the parent's sweep.
  * Direct products of small non-abelian groups (Heisenberg mod 5, 7 and SL(2,5), SL(2,7)) with Z_k.
  * Two tiers.  Tier 1 has |G| in [2001, 2400], so a valid graph beats the record 4000 and is returned at once.
    Tier 2 has |G| in [1792, 2000] and is the safe target.  The first valid tier-2 graph is kept while
    tier-1 search continues.  If nothing is found, a fallback Haar graph is tried, then K_{d,d}.

Every returned graph passes lib.is_valid.
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


def group_affine(p, k, M):
    """V x| Z_k with V = Z_p^2, element (v, j) coded as ((x*p + y) * k + j), and (v, j)(w, l) = (v + M^j w, j + l).
    M is a 2x2 matrix given as (a, b, c, d) with M^k = I mod p."""
    a, b, c, dd = M
    Mm = np.array([[a, b], [c, dd]], dtype=np.int64)
    P = np.zeros((k, 2, 2), dtype=np.int64)
    cur = np.eye(2, dtype=np.int64)
    for j in range(k):
        P[j] = cur
        cur = (cur @ Mm) % p
    if not (cur == np.eye(2, dtype=np.int64)).all():
        raise ValueError("M^k != I")
    N = p * p * k
    g = np.arange(N, dtype=np.int64)
    x = (g // k) // p
    y = (g // k) % p
    jj = g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 128):
        hi = min(N, lo + 128)
        Pi = P[jj[lo:hi]]
        xi = x[lo:hi, None]
        yi = y[lo:hi, None]
        nx = (xi + Pi[:, 0, 0, None] * x[None, :] + Pi[:, 0, 1, None] * y[None, :]) % p
        ny = (yi + Pi[:, 1, 0, None] * x[None, :] + Pi[:, 1, 1, None] * y[None, :]) % p
        nj = (jj[lo:hi, None] + jj[None, :]) % k
        MT[lo:hi] = (nx * p + ny) * k + nj
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
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

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


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def _mm2(A, B, p):
    """Product of two 2x2 matrices over Z_p, each given as (a, b, c, d)."""
    a, b, c, d = A
    e, f, g, h = B
    return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)


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
    """Annealing over d-subsets of the group.  Candidate replacements mix random elements with products of two
    current set elements.  Restarts from a random set when stuck.  Returns (best S, best cost)."""
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
        half = K // 2
        Xr = rng.integers(0, N, size=K - half)
        pa = S[rng.integers(0, d, size=half)]
        pb = S[rng.integers(0, d, size=half)]
        Xp = MT[inv[pa], pb] if half > 0 else np.zeros(0, dtype=np.int32)
        X = np.concatenate([Xr, Xp]).astype(np.int32)
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
SLICE = 3.5   # seconds of annealing per candidate group

FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def metacyclic_candidates(lo, hi):
    """All (N, 'meta', (m, k, lam)) with N = m*k in [lo, hi], k >= 2, m >= 3, lam a unit mod m with lam^k = 1."""
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
    """Heisenberg mod p and SL(2, p) in the order range."""
    out = []
    for p in (7, 11, 13):
        N = p ** 3
        if lo <= N <= hi:
            out.append((N, "heis", (p,)))
        N = p * (p * p - 1)
        if lo <= N <= hi:
            out.append((N, "sl2", (p,)))
    return out


def affine_candidates(lo, hi, rng, per_key=6):
    """Groups Z_p^2 x| Z_k for p in (5, 7, 11): the generator of Z_k acts by M with M^k = I mod p."""
    out = []
    for p in (5, 7, 11):
        ks = [k for k in range(2, hi // (p * p) + 2) if lo <= p * p * k <= hi]
        if not ks:
            continue
        kmax = max(ks)
        orders = {}
        ident = (1, 0, 0, 1)
        for M in itertools.product(range(p), repeat=4):
            a, b, c, dd = M
            if (a * dd - b * c) % p == 0 or M == ident:
                continue
            X, r = M, 1
            while X != ident and r < kmax:
                X = _mm2(X, M, p)
                r += 1
            if X == ident:
                orders.setdefault(r, []).append(M)
        for k in ks:
            mats = [M for r, lst in orders.items() if k % r == 0 for M in lst]
            if not mats:
                continue
            pick = rng.permutation(len(mats))[:per_key]
            for t in pick:
                out.append((p * p * k, "aff", (p, k, mats[int(t)])))
    return out


def tcyc_candidates(lo, hi):
    """Small non-abelian groups times Z_k."""
    out = []
    bases = [(("heis", (5,)), 125), (("heis", (7,)), 343), (("sl2", (5,)), 120), (("sl2", (7,)), 336)]
    for (bk, ba), bo in bases:
        for k in range(2, hi // bo + 1):
            N = bo * k
            if lo <= N <= hi:
                out.append((N, "tcyc", (bk, ba, k)))
    return out


def candidates(lo, hi, rng):
    return (metacyclic_candidates(lo, hi) + special_candidates(lo, hi)
            + affine_candidates(lo, hi, rng) + tcyc_candidates(lo, hi))


def make_group(kind, args):
    """Build (MT, inv) for a candidate."""
    if kind == "meta":
        return group_meta(*args)
    if kind == "heis":
        return group_heis(*args)
    if kind == "sl2":
        return group_sl2(*args)
    if kind == "aff":
        p, k, M = args
        return group_affine(p, k, M)
    if kind == "tcyc":
        bk, ba, k = args
        return group_times_cyclic(make_group(bk, ba), k)
    raise ValueError(kind)


def run(d, D, seed, time_limit):
    """Tiered annealing.  A valid graph with |G| > 2000 beats the record and is returned at once.
    Otherwise the best valid tier-2 graph (|G| in [1792, 2000]) is returned at the end."""
    t0 = time.monotonic()
    budget_end = t0 + max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = np.random.default_rng(seed)

    tier1 = candidates(2001, 2400, rng)
    tier2 = candidates(1792, 2000, rng)
    for lst in (tier1, tier2):
        rng.shuffle(lst)
        lst.sort(key=lambda c: c[0])

    best2 = None
    i1 = i2 = 0
    step = 0
    while time.monotonic() < budget_end - 0.5:
        step += 1
        use2 = bool(tier2) and best2 is None and (not tier1 or step % 4 == 0)
        if use2:
            cand = tier2[i2 % len(tier2)]
            i2 += 1
        elif tier1:
            cand = tier1[i1 % len(tier1)]
            i1 += 1
        else:
            break
        _, kind, args = cand
        slice_end = min(budget_end, time.monotonic() + SLICE)
        try:
            MT, inv = make_group(kind, args)
            S, c = search(MT, inv, d, slice_end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                if g[0] > 4000:
                    return g
                if best2 is None or g[0] > best2[0]:
                    best2 = g
    if best2 is not None:
        return best2

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
    return run(d, D, seed, time_limit)
