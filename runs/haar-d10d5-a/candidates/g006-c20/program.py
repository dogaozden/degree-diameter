"""Targeted-move Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

A Haar graph over a group G with connection set S (|S| = d) has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G. The search minimises the number of uncovered group
elements on both sides (cost 0 = valid). New in this version: a targeted proposal move.
Half of the candidate replacements for slot i are "neighbours of uncovered elements":
x = s^-1 u or u s^-1 for a random uncovered element u and a random other set element s.
This aims the search at the gaps instead of sampling blindly. Only a graph checked with
lib.is_valid is returned; otherwise a smaller valid fallback is used.
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
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l)."""
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
    """Table of a group given as an (N, c) integer coordinate array (element 0 = identity)."""
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
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p,
                         (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q):
    """AGL(1, q) = GF(q) x| GF(q)^*, order q(q-1), q a prime power."""
    F = lib.GF(q)
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in range(1, q) if (b, a) != (0, 1)],
                 dtype=np.int64)
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
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
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
    """Uncovered elements, both sides (cost 0 = valid)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def uncovered(MT, inv, S):
    """Array of the group elements left uncovered on either side by the current S."""
    N = MT.shape[0]
    out = [np.nonzero(~_cover(MT, N, np.unique(P)))[0] for P in _pairs(MT, inv, S)]
    return np.concatenate(out).astype(np.int64)


def batch_costs(MT, inv, S, i, X):
    """cost of S with slot i replaced by x, for every x in the int array X."""
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


def propose(MT, inv, S, i, rng, K, unc):
    """Candidate replacements for slot i: half random, half aimed at uncovered elements."""
    N = MT.shape[0]
    rest = np.delete(S, i)
    n_t = K // 2 if len(unc) else 0
    parts = [rng.integers(0, N, size=K - n_t)]
    if n_t:
        u = unc[rng.integers(len(unc), size=n_t)]
        s = rest[rng.integers(len(rest), size=n_t)]
        si = inv[s]
        xt = np.where(rng.random(n_t) < 0.5, MT[si, u], MT[u, si])
        parts.append(xt)
    X = np.unique(np.concatenate(parts).astype(np.int32))
    return X[~np.isin(X, rest)]


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Annealing over d-subsets containing 0, with targeted proposals and restarts.
    Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

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
        unc = uncovered(MT, inv, S)
        X = propose(MT, inv, S, i, rng, K, unc)
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
            S = None
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
    cands = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        cands.append(lambda: lib.projective_plane_incidence(d - 1))
    if d >= 1 and D >= 1:
        cands.append(lambda: lib.haar_graph(d, range(d)))
    for make in cands:
        try:
            n, edges = make()
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            pass
    if d >= 1 and D >= 1:
        return 2, [(0, 1)]
    return 1, []


# ======================================================================================== cell: d10D5
TARGET = (10, 5)
LO, HI = 2001, 2100          # group orders just above 2000 (2|G| > 4000 needs |G| > 2000)
NUM_GROUPS = 6               # groups sharing the main budget
RESERVE_LO, RESERVE_HI = 1500, 1800  # fallback search range if the main search fails


def metacyclic_specs(lo, hi):
    """Specs ('meta', m, k, lam) for Z_m x|_lam Z_k with lo <= m*k <= hi and lam != 1."""
    out = []
    for k in range(2, 11):
        for m in range(max(2, -(-lo // k)), hi // k + 1):
            if m * k < lo or m * k > hi:
                continue
            found = 0
            for lam in range(2, min(m, 400)):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append(('meta', m, k, lam))
                    found += 1
                    if found >= 2:
                        break
    return out


def make_builder(spec):
    kind = spec[0]
    if kind == 'meta':
        _, m, k, lam = spec
        return lambda: group_meta(m, k, lam)
    if kind == 'sl2':
        return lambda: group_times_cyclic(group_sl2(7), 6)
    if kind == 'heis':
        return lambda: group_times_cyclic(group_heis(7), 6)
    if kind == 'agl':
        return lambda: group_times_cyclic(group_agl(13), 13)
    raise ValueError(kind)


# Previously found valid Haar graph over Z_199 x| Z_9 (order 1791), checked at run time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def run_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    main_end = t0 + 0.72 * time_limit
    rng = np.random.default_rng(seed)

    pool = metacyclic_specs(LO, HI) + [('sl2',), ('heis',), ('agl',)]
    order = rng.permutation(len(pool))
    chosen = [pool[i] for i in order[:NUM_GROUPS]]

    for n_done, spec in enumerate(chosen):
        now = time.monotonic()
        if now >= main_end:
            break
        end = now + (main_end - now) / (len(chosen) - n_done)
        try:
            MT, inv = make_builder(spec)()
            S, c = search(MT, inv, d, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g

    # Reserve: a known valid Haar graph, then a short search over smaller groups.
    try:
        MT, _ = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass

    reserve_end = t0 + 0.85 * time_limit
    try:
        specs = metacyclic_specs(RESERVE_LO, RESERVE_HI)
        if specs:
            spec = specs[int(rng.integers(len(specs)))]
            MT, inv = make_builder(spec)()
            S, c = search(MT, inv, d, reserve_end, rng)
            if S is not None and c == 0:
                g = checked(MT, S, d, D)
                if g is not None:
                    return g
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    try:
        if (d, D) == TARGET:
            g = run_target(d, D, seed, time_limit)
        else:
            g = trivial(d, D)
        n, edges = g
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
