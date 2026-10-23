"""Haar-graph search for the bipartite degree-diameter problem, diameter 5 (numpy only).

THEORY.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A), (g, B) and edges
(g, A) ~ (s*g, B).  It is bipartite, d-regular, has 2|G| vertices, and has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements on both sides; cost 0 means valid.

CHANGES FROM THE PARENT.
  * Two phases.  Phase 1 secures a checked baseline with |G| in [1792, 2000] (3584+ vertices).  Phase 2 hunts
    for |G| in [2001, 2800], which is needed to beat 4000.
  * New non-metacyclic family: affine groups AGL(1, p) = Z_p x| Z_{p-1}, for p = 47 (order 2162) and p = 53
    (order 2756).  These are tried first in phase 2, along with Heis(13) and SL(2, 13).
  * Vectorised metacyclic candidate enumeration (the parent's pure-Python loop would be too slow over a wider range).
  * Basin-hopping restarts: when the annealer stalls, it perturbs the best set (three slots replaced) half the time,
    and restarts from a random set otherwise.

SAFETY.  Only graphs passing lib.is_valid are returned.  The largest valid graph found is kept.  If phase 1 and
phase 2 both fail, a precomputed valid Haar graph is used, and as a last resort a small always-valid graph.
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


def group_agl(p):
    """AGL(1, p) for a prime p: maps x -> a*x + b, element (a, b) with a in Z_p^*, b in Z_p; order p(p-1).
    Product (a, b)(c, d) = (ac, ad + b) (composition)."""
    els = [(1, 0)] + [(a, b) for a in range(1, p) for b in range(p) if (a, b) != (1, 0)]
    e = np.array(els, dtype=np.int64)

    def mul(X, Y):
        a, b = X[..., 0], X[..., 1]
        c, d = Y[..., 0], Y[..., 1]
        return np.stack([(a * c) % p, (a * d + b) % p], axis=-1)
    return _table_from_coords(e, mul)


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


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=3000):
    """Annealing over d-subsets of the group, with product moves.  When stalled, it either perturbs the best
    set (three slots replaced) or restarts from a random set.  Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    def perturb(base):
        T = base.copy()
        for i in rng.choice(d, 3, replace=False):
            while True:
                x = int(rng.integers(0, N))
                if x not in T:
                    break
            T[i] = x
        return T.astype(np.int32)

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
            if best is not None and rng.random() < 0.5:
                S = perturb(best)
            else:
                S = None
            cur = None
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

PHASE1 = (1792, 2000)   # baseline: any valid Haar graph here gives >= 3584 vertices
PHASE2 = (2001, 2800)   # any valid Haar graph here gives > 4000 vertices
SLICE1 = 2.0
SLICE2 = 3.0
FRAC_PHASE1 = 0.30      # share of time_limit for the baseline phase
FRAC_END = 0.80         # share of time_limit for all search

FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])

# Non-metacyclic groups: (kind, args, order)
SPECIALS = [
    ("heis", (13,), 13 ** 3),
    ("sl2", (13,), 13 * (13 * 13 - 1)),
    ("agl", (47,), 47 * 46),
    ("agl", (53,), 53 * 52),
]


def meta_candidates(lo, hi, max_k=12):
    """Metacyclic (N, 'meta', (m, k, lam)) with N = m*k in [lo, hi], 2 <= k <= max_k, m >= 3, lam^k = 1 mod m."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, min(max_k, N - 1) + 1):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lam = np.arange(2, m, dtype=np.int64)
            ok = np.gcd(lam, m) == 1
            x = lam.copy()
            for _ in range(k - 1):
                x = (x * lam) % m
            ok &= (x == 1 % m)
            for l in lam[ok]:
                out.append((N, "meta", (m, k, int(l))))
    return out


def special_candidates(lo, hi):
    """Non-metacyclic candidates with order in [lo, hi]."""
    return [(N, kind, args) for kind, args, N in SPECIALS if lo <= N <= hi]


def make_group(kind, args):
    """Build (MT, inv) for a candidate."""
    if kind == "meta":
        return group_meta(*args)
    if kind == "heis":
        return group_heis(*args)
    if kind == "sl2":
        return group_sl2(*args)
    if kind == "agl":
        return group_agl(*args)
    raise ValueError(kind)


def _shuffled_by_order(cands, rng):
    """Group candidates by order, shuffle within each order, and list orders ascending."""
    keyed = {}
    for c in cands:
        keyed.setdefault(c[0], []).append(c)
    out = []
    for N in sorted(keyed):
        grp = keyed[N]
        rng.shuffle(grp)
        out.extend(grp)
    return out


def run(d, D, seed, time_limit):
    """Two-phase search.  Returns the largest checked valid Haar graph found, or None."""
    t0 = time.monotonic()
    end = t0 + FRAC_END * time_limit
    phase1_end = t0 + FRAC_PHASE1 * time_limit
    rng = np.random.default_rng(seed)
    best = None

    def consider(g):
        nonlocal best
        if g is not None and (best is None or g[0] > best[0]):
            best = g

    # Phase 1: secure a baseline (ascending order, stop at the first valid graph).
    order1 = _shuffled_by_order(meta_candidates(*PHASE1), rng)
    idx = 0
    while order1 and best is None:
        if time.monotonic() >= phase1_end:
            break
        _, kind, args = order1[idx % len(order1)]
        idx += 1
        slice_end = min(time.monotonic() + SLICE1, phase1_end)
        try:
            MT, inv = make_group(kind, args)
            S, c = search(MT, inv, d, slice_end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            consider(checked(MT, S, d, D))

    # Phase 2: the hunt for orders above 2000.  Non-metacyclic groups first, then metacyclic, round robin.
    specials = special_candidates(*PHASE2)
    rng.shuffle(specials)
    metas = _shuffled_by_order(meta_candidates(*PHASE2), rng)
    order2 = specials + metas
    idx = 0
    while order2:
        now = time.monotonic()
        remaining = end - now
        if remaining < 1.0:
            break
        _, kind, args = order2[idx % len(order2)]
        idx += 1
        slice_end = now + min(SLICE2, remaining)
        try:
            MT, inv = make_group(kind, args)
            S, c = search(MT, inv, d, slice_end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            consider(checked(MT, S, d, D))

    return best


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        g = run(d, D, seed, time_limit)
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
