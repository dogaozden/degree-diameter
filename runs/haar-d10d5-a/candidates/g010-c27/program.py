"""Multi-group Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

A Haar graph over a group G with connection set S (|S| = d) has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G. The search minimises the uncovered count (cost) by annealing.

New in this version:
  * greedy_init: builds S one element at a time, each step choosing the candidate that
    minimises the cost of the partial set. Used for restarts instead of pure random sets.
  * propose: candidate moves mix random group elements, conjugates g*s*g^-1 of current
    elements, and products of two current elements, so the search can move within
    structured neighbourhoods as well as jump at random.
  * Groups are chosen at random from metacyclic Z_m x| Z_k of order in [2001, 2100] plus
    SL(2,7)xZ_6, Heis(7)xZ_6 and AGL(1,13)xZ_13.

Only a graph checked with lib.is_valid is returned; otherwise a valid smaller graph is returned.
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
    """GF(q) x| C_k (default k = q-1, that is AGL(1, q)). q a prime power."""
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


# ------------------------------------------------------------------------------------------------ search core

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
    """Cost of S with slot i replaced by x, for every x in the int array X."""
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


# ------------------------------------------------------------------ new helpers: greedy init and proposals

def greedy_init(MT, inv, d, rng, cands=48):
    """Build a d-set containing 0 one element at a time, each step taking the candidate of least partial cost.

    Left translation by a group element preserves validity, so WLOG 0 is in S.
    """
    N = MT.shape[0]
    S = np.array([0], dtype=np.int32)
    while len(S) < d:
        pool = np.unique(rng.integers(1, N, size=cands))
        pool = pool[~np.isin(pool, S)]
        if len(pool) == 0:
            continue
        best_c, best_v = int(pool[0]), None
        for c in pool:
            T = np.append(S, np.int32(c)).astype(np.int32)
            v = cost(MT, inv, T) + rng.random() * 0.5
            if best_v is None or v < best_v:
                best_v, best_c = v, int(c)
        S = np.append(S, np.int32(best_c)).astype(np.int32)
    return S


def propose(MT, inv, S, i, rng, K):
    """Candidate replacements for slot i: random elements, conjugates g*s*g^-1, and products s_a*s_b of set elements."""
    N = MT.shape[0]
    rest = np.delete(S, i)
    r = len(rest)
    n_rand = K // 2
    n_conj = K // 4
    n_prod = K - n_rand - n_conj
    rnd = rng.integers(1, N, size=n_rand)
    g = rng.integers(0, N, size=n_conj)
    s = rest[rng.integers(0, r, size=n_conj)]
    conj = MT[MT[g, s], inv[g]]
    a = rest[rng.integers(0, r, size=n_prod)]
    b = rest[rng.integers(0, r, size=n_prod)]
    prod = MT[a, b]
    X = np.unique(np.concatenate([rnd, conj, prod]).astype(np.int32))
    X = X[~np.isin(X, rest)]
    return X


def search(MT, inv, d, deadline, rng, K=32, temp=0.45, patience=3000):
    """Simulated annealing over d-subsets of the group with restarts. Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0
    while time.monotonic() < deadline:
        if S is None:
            u = rng.random()
            if best is not None and u < 0.4:
                S = best.copy()
                for i in rng.choice(d, 2, replace=False):
                    S[i] = rng.integers(1, N)
                if len(set(S.tolist())) < d:
                    S = None
                    continue
            elif u < 0.75:
                S = greedy_init(MT, inv, d, rng)
            else:
                S = np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)
            cur = None
        if cur is None:
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = S.copy(), cur
            if cur == 0:
                return best, 0
        i = int(rng.integers(d))
        X = propose(MT, inv, S, i, rng, K)
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
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ======================================================================================== cell: d10D5
TARGET = (10, 5)
LO, HI = 2001, 2100          # group orders just above the threshold 2000 (2|G| > 4000 needs |G| > 2000)
NUM_GROUPS = 5               # how many groups share the budget


def metacyclic_specs(lo, hi):
    """Specs (order, 'meta', m, k, lam) for Z_m x|_lam Z_k with lo <= m*k <= hi and lam != 1."""
    out = []
    for k in range(2, 11):
        for m in range(max(2, -(-lo // k)), hi // k + 1):
            if m * k < lo or m * k > hi:
                continue
            lams = []
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    lams.append(lam)
                    if len(lams) >= 2:
                        break
            for lam in lams:
                out.append((m * k, 'meta', m, k, lam))
    return out


SPECIALS = [(2016, 'sl2'), (2058, 'heis'), (2028, 'agl', 13, 13)]


def make_builder(spec):
    kind = spec[1]
    if kind == 'meta':
        _, _, m, k, lam = spec
        return lambda: group_meta(m, k, lam)
    if kind == 'sl2':
        return lambda: group_times_cyclic(group_sl2(7), 6)
    if kind == 'heis':
        return lambda: group_times_cyclic(group_heis(7), 6)
    if kind == 'agl':
        q, k = spec[2], spec[3]
        return lambda: group_times_cyclic(group_agl(q), k)
    raise ValueError(kind)


# Valid smaller Haar graph (order 1791 group, 3582 vertices), checked at run time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def run_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)

    pool = metacyclic_specs(LO, HI) + SPECIALS
    order = rng.permutation(len(pool))
    chosen = [pool[i] for i in order[:NUM_GROUPS]]

    for n_done, spec in enumerate(chosen):
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) / (len(chosen) - n_done)
        try:
            MT, inv = make_builder(spec)()
            S, c = search(MT, inv, d, end, rng)
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
        n, edges = trivial(d, D)
    else:
        n, edges = run_target(d, D, seed, time_limit)
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return 1, []
