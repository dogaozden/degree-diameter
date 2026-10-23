"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A) and (g, B),
with edges (g, A) ~ (s*g, B). It is bipartite, d-regular, and has 2|G| vertices. Its diameter is at most 5
iff (S^-1 S)^2 = G and (S S^-1)^2 = G. COST(S) counts the uncovered elements on both sides.

NEW IN THIS VERSION.
  * Vector semidirect groups Z_p^dim x| Z_k (group_vsd): Z_k acts on Z_p^dim by a random matrix M with
    M^k = I and M != I. These are nonabelian groups with no cyclic normal subgroup of the metacyclic kind.
    Orders 2001..2200 are covered by (p, dim, k) choices such as 5^2*81, 7^2*42, 11^2*18, 13^2*13, 2^3*257.
  * Central-product-free direct products of small nonabelian groups with cyclic groups (group_times_cyclic):
    SL(2,7) x Z_6 (order 2016), SL(2,5) x Z_17 (2040), Heis(5) x Z_17 (2125), and similar.
  * Targeted moves (targeted_cands): pick an uncovered element u on one side, a random pair product q from the
    current set, and set p = u q^-1. Then choose the slot value x so that the pair product containing x equals
    p. This directly covers u, so it is a more informed move than random replacement.
  * Groups of order above 2000 are tried first, and only a valid graph with more than 4000 vertices is returned
    at once. Smaller valid Haar graphs are kept as fallbacks.

Only checked graphs (lib.is_valid) are returned. Other (d, D) pairs get a small always-valid graph.
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


def group_vsd(p, dim, k, M):
    """Z_p^dim x| Z_k where the generator of Z_k acts by the matrix M (M^k = I mod p).
    Element (v, j) has index code(v)*k + j, with code(v) = sum v_i p^i, and (v, j)(w, l) = (v + M^j w, j + l)."""
    M = np.asarray(M, dtype=np.int64) % p
    P = p ** dim
    V = np.array([[(c // p ** i) % p for i in range(dim)] for c in range(P)], dtype=np.int64)
    wts = p ** np.arange(dim, dtype=np.int64)
    Mp = [np.eye(dim, dtype=np.int64)]
    for _ in range(1, k):
        Mp.append((Mp[-1] @ M) % p)
    N = P * k
    jl = np.arange(k, dtype=np.int64)
    MT = np.empty((N, N), dtype=np.int32)
    for v in range(P):
        vv = V[v]
        for j in range(k):
            img = (vv[None, :] + V @ Mp[j].T) % p          # row w holds v + M^j w
            codes = img @ wts
            MT[v * k + j] = (codes[:, None] * k + ((j + jl) % k)[None, :]).ravel()
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


# ---------------------------------------------------------------- random semidirect action matrices

def _det_mod(M, p):
    """Determinant of a small integer matrix, reduced mod p (dim <= 4)."""
    dim = M.shape[0]
    det = 0
    for perm in itertools.permutations(range(dim)):
        inv_count = sum(1 for a in range(dim) for b in range(a + 1, dim) if perm[a] > perm[b])
        prod = 1
        for r in range(dim):
            prod *= int(M[r, perm[r]])
        det += -prod if inv_count % 2 else prod
    return det % p


def _matpow(M, e, p):
    """M**e mod p by repeated squaring."""
    dim = M.shape[0]
    R = np.eye(dim, dtype=np.int64)
    B = M % p
    while e:
        if e & 1:
            R = (R @ B) % p
        B = (B @ B) % p
        e >>= 1
    return R


def _rand_vsd(p, dim, k, rng, tries=120, want=3):
    """Random non-identity matrices M over Z_p with M^k = I and det != 0."""
    out = []
    I = np.eye(dim, dtype=np.int64)
    for _ in range(tries):
        M = rng.integers(0, p, (dim, dim)).astype(np.int64)
        if _det_mod(M, p) == 0:
            continue
        if np.array_equal(M % p, I):
            continue
        if not np.array_equal(_matpow(M, k, p), I):
            continue
        out.append(M)
        if len(out) >= want:
            break
    return out


def vsd_candidates(lo, hi, rng):
    """Vector semidirect groups Z_p^dim x| Z_k with order N = p^dim * k in [lo, hi]."""
    out = []
    for p, dim in ((2, 3), (2, 4), (3, 2), (3, 3), (5, 2), (7, 2), (11, 2), (13, 2)):
        base = p ** dim
        k_lo = max(2, -(-lo // base))
        k_hi = hi // base
        for k in range(k_lo, k_hi + 1):
            for M in _rand_vsd(p, dim, k, rng):
                out.append((base * k, "vsd", (p, dim, k, tuple(int(x) for x in M.flatten()))))
    return out


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


def targeted_cands(MT, inv, S, i, rng, cnt):
    """Candidate slot values that directly cover an uncovered element.
    Pick an uncovered u on one side and a current pair product q on that side; let p = u q^-1.
    Side 0: x = s p makes s^-1 x = p, so p q = u. Side 1: x makes s x^-1 = p, so p q = u.
    Here s is a random other set element."""
    N = MT.shape[0]
    rest = np.delete(S, i)
    P0, P1 = _pairs(MT, inv, S)
    U0, U1 = np.unique(P0), np.unique(P1)
    unc = [np.flatnonzero(~_cover(MT, N, U0)), np.flatnonzero(~_cover(MT, N, U1))]
    out = []
    for _ in range(cnt):
        side = int(rng.integers(2))
        if len(unc[side]) == 0:
            continue
        u = int(unc[side][rng.integers(len(unc[side]))])
        Q = U0 if side == 0 else U1
        q = int(Q[rng.integers(len(Q))])
        p = int(MT[u, inv[q]])
        s = int(rest[rng.integers(len(rest))])
        if side == 0:
            x = int(MT[s, p])
        else:
            x = int(inv[MT[inv[s], p]])
        out.append(x)
    return np.array(out, dtype=np.int32)


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Annealing over d-subsets of the group. Each step proposes K replacements for one slot, split into random
    elements, product moves x = y_a * y_b, and targeted moves that cover an uncovered element.
    Restarts from a random set when stuck. Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0
    third = K // 3

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
        Xr = rng.integers(0, N, size=K - 2 * third)
        pa = S[rng.integers(0, d, size=third)]
        pb = S[rng.integers(0, d, size=third)]
        Xp = MT[inv[pa], pb]
        Xt = targeted_cands(MT, inv, S, i, rng, third)
        X = np.concatenate([Xr, Xp, Xt]).astype(np.int32)
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

LO_LOW, HI = 1792, 2200   # valid Haar graph with |G| in [1792, 2000] is a fallback
BEAT_N = 2001             # |G| >= 2001 gives 2|G| >= 4002 > record 4000
SLICE = 2.5               # seconds of annealing per candidate group

FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


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
    for p in (3, 5, 7, 11, 13):
        N = p ** 3
        if lo <= N <= hi:
            out.append((N, "heis", (p,)))
        N = p * (p * p - 1)
        if lo <= N <= hi:
            out.append((N, "sl2", (p,)))
    return out


def product_candidates(lo, hi):
    """Direct products of small nonabelian groups with Z_k, order n0*k in [lo, hi]."""
    out = []
    for kind, args, n0 in (("sl2", (3,), 24), ("sl2", (5,), 120), ("sl2", (7,), 336),
                           ("heis", (3,), 27), ("heis", (5,), 125)):
        for k in range(2, hi // n0 + 1):
            N = n0 * k
            if lo <= N <= hi:
                out.append((N, "tcyc", (kind, args, k)))
    return out


def make_group(kind, args):
    """Build (MT, inv) for a candidate."""
    if kind == "meta":
        return group_meta(*args)
    if kind == "heis":
        return group_heis(*args)
    if kind == "sl2":
        return group_sl2(*args)
    if kind == "vsd":
        p, dim, k, flat = args
        return group_vsd(p, dim, k, np.array(flat, dtype=np.int64).reshape(dim, dim))
    if kind == "tcyc":
        inner_kind, inner_args, k = args
        return group_times_cyclic(make_group(inner_kind, inner_args), k)
    raise ValueError(kind)


def run_meta(d, D, seed, time_limit):
    """Round-robin annealing over candidate groups. Groups of order >= BEAT_N are tried first, with the
    smaller ones on every fourth slice. A valid graph with more than 4000 vertices is returned at once.
    Otherwise the largest valid graph found is returned."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.85 * time_limit
    rng = np.random.default_rng(seed)

    new_fams = vsd_candidates(LO_LOW, HI, rng) + product_candidates(LO_LOW, HI) + special_candidates(LO_LOW, HI)
    meta = metacyclic_candidates(LO_LOW, HI)

    def shuffled(lst):
        idx = rng.permutation(len(lst))
        return [lst[i] for i in idx]

    high = shuffled([c for c in new_fams if c[0] >= BEAT_N]) + shuffled([c for c in meta if c[0] >= BEAT_N])
    low = shuffled([c for c in new_fams if c[0] < BEAT_N]) + shuffled([c for c in meta if c[0] < BEAT_N])

    best_low = None
    ih = il = 0
    step = 0
    while True:
        now = time.monotonic()
        remaining = deadline_all - now
        if remaining < 0.5:
            break
        if low and ((step % 4 == 3) or not high):
            c = low[il % len(low)]
            il += 1
        elif high:
            c = high[ih % len(high)]
            ih += 1
        else:
            break
        step += 1
        _, kind, args = c
        slice_end = min(now + SLICE, deadline_all)
        try:
            MT, inv = make_group(kind, args)
            S, cst = search(MT, inv, d, slice_end, rng)
        except Exception:
            continue
        if S is not None and cst == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                if g[0] > 4000:
                    return g
                if best_low is None or g[0] > best_low[0]:
                    best_low = g

    if best_low is not None:
        return best_low
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
