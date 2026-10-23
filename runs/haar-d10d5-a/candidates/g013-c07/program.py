"""Haar-graph seed programs for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  Let G be a finite group and S a subset of G with |S| = d.  The Haar graph has vertices (g, A) and
(g, B) for g in G, with edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, and has 2|G| vertices.
Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements on both
sides; cost 0 means valid.

THIS VERSION.
  * Record-first search: a Haar graph on 2|G| vertices beats the d=10, D=5 record of 4000 exactly when |G| >= 2001.
    The search now spends the first 70% of the budget only on groups with |G| in [2001, 2200].
  * The remaining time goes to the older range [1792, 2000], so a valid graph is still returned if no group above
    2000 is found.  Any valid graph, not just the record one, is returned as soon as it is found.
  * The unverified hard-coded fallback group is removed.  Its order (1791) did not match the parent's valid
    3584-vertex result, so it was never a reliable safety net.

Only checked graphs (lib.is_valid) are returned.  If nothing is found, a small always-valid graph is returned.
Every other (d, D) gets a small always-valid graph.
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
    """Annealing over d-subsets of the group.  Candidate replacements mix random elements with products of two
    current set elements (the product move).  Restarts from a random set when stuck.
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

RECORD_ORDER = 2001   # a Haar graph on 2|G| vertices beats the record 4000 iff |G| >= 2001
HI = 2200             # upper end of the search range
LO = 1792             # lower end of the fallback range
HI_FRACTION = 0.70    # fraction of the budget spent on the record-beating range
SLICE = 4.0           # seconds of annealing per candidate group


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
    """Non-metacyclic groups in the order range: Heisenberg mod p and SL(2, p)."""
    out = []
    for p in (7, 11, 13):
        N = p ** 3
        if lo <= N <= hi:
            out.append((N, "heis", (p,)))
        N = p * (p * p - 1)
        if lo <= N <= hi:
            out.append((N, "sl2", (p,)))
    return out


def make_group(kind, args):
    """Build (MT, inv) for a candidate."""
    if kind == "meta":
        return group_meta(*args)
    if kind == "heis":
        return group_heis(*args)
    if kind == "sl2":
        return group_sl2(*args)
    raise ValueError(kind)


def ordered_candidates(lo, hi, rng):
    """Candidates with order in [lo, hi], grouped by order ascending, shuffled within each order."""
    cands = metacyclic_candidates(lo, hi) + special_candidates(lo, hi)
    keyed = {}
    for c in cands:
        keyed.setdefault(c[0], []).append(c)
    out = []
    for N in sorted(keyed):
        grp = keyed[N]
        rng.shuffle(grp)
        out.extend(grp)
    return out


def sweep(cands, deadline, d, D, rng):
    """Round-robin annealing over candidate groups until the deadline.  Returns the first checked valid graph, or None."""
    if not cands:
        return None
    idx = 0
    while time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.5:
            break
        _, kind, args = cands[idx % len(cands)]
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
    return None


def run_meta(d, D, seed, time_limit):
    """Record-first search: groups with |G| in [RECORD_ORDER, HI] get the first HI_FRACTION of the budget,
    then groups with |G| in [LO, RECORD_ORDER - 1] get the rest.  Returns the first checked valid Haar graph."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.88 * time_limit
    deadline_hi = t0 + HI_FRACTION * 0.88 * time_limit
    rng = np.random.default_rng(seed)

    hi_cands = ordered_candidates(RECORD_ORDER, HI, rng)
    lo_cands = ordered_candidates(LO, RECORD_ORDER - 1, rng)

    g = sweep(hi_cands, deadline_hi, d, D, rng)
    if g is not None:
        return g
    g = sweep(lo_cands, deadline_all, d, D, rng)
    if g is not None:
        return g
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run_meta(d, D, seed, time_limit)
