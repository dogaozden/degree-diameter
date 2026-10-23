"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

A Haar graph over a group G with connection set S (|S| = d) has vertices (g, A), (g, B) and
edges (g, A) ~ (s*g, B) for s in S. It has diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.

Changes from the parent:
  * Exact batched cost: every candidate is scored by a full recomputation, vectorised over K
    candidates at once. This avoids the incremental bookkeeping, which was the most error-prone part.
  * Identity is fixed in slot 0. Left-translating S preserves the cost, so this loses nothing.
  * New proposal operator (conjugate / product moves): a new slot value is drawn as a uniform
    element, a conjugate g t g^-1 of a current element, or a product of two current elements.
    Conjugates keep the group-theoretic structure of S, and products reach words the uniform
    moves rarely hit.
  * Only lib.is_valid-checked graphs are returned. The fallback is a Haar graph that was valid for
    the parent, then K_{d,d} or a projective-plane graph.
"""
import itertools
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + lam^j b, j + l)."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def _table_from_coords(elems, mulfun):
    """Table of a group given by an (N, c) coordinate array (row 0 = identity) and a vectorised product."""
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
    """SL(2, p) for prime p, order p(p^2-1); identity placed at index 0."""
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
    """AGL(1, q) = GF(q) x| GF(q)^*, identity at index 0."""
    F = lib.GF(q)
    k = q - 1
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# --------------------------------------------------------------------------- cost

def batch_cost(MT, inv, Ss):
    """Uncovered elements (both sides) for each row of the (K, d) int64 array Ss. 0 = valid."""
    K, d = Ss.shape
    N = MT.shape[0]
    Si = inv[Ss]
    out = np.zeros(K, dtype=np.int64)
    offs = (np.arange(K, dtype=np.int64) * N)[:, None, None]
    sides = (MT[Si[:, :, None], Ss[:, None, :]], MT[Ss[:, :, None], Si[:, None, :]])
    for A in sides:
        A = A.reshape(K, d * d).astype(np.int64)
        P = MT[A[:, :, None], A[:, None, :]].astype(np.int64) + offs
        cov = np.zeros(K * N, dtype=bool)
        cov[P.ravel()] = True
        out += N - cov.reshape(K, N).sum(axis=1)
    return out


# ------------------------------------------------------------ proposal operator

def propose(MT, inv, S, K, rng):
    """K candidate values: uniform, conjugate g t g^-1 of a current element, or product s_j s_l."""
    N = MT.shape[0]
    d = len(S)
    kind = rng.integers(0, 3, size=K)
    uni = rng.integers(0, N, size=K)
    t = S[rng.integers(0, d, size=K)]
    g = rng.integers(0, N, size=K)
    conj = MT[MT[g, t], inv[g]]
    j = S[rng.integers(0, d, size=K)]
    l = S[rng.integers(0, d, size=K)]
    prod = MT[j, l]
    X = np.where(kind == 1, conj, np.where(kind == 2, prod, uni))
    return X.astype(np.int64)


def anneal(MT, inv, d, deadline, rng, K=32, temp=0.6, patience=3000):
    """Annealing over sets S with 0 fixed in slot 0. Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 18
    while time.monotonic() < deadline:
        S = np.empty(d, dtype=np.int64)
        S[0] = 0
        S[1:] = rng.choice(np.arange(1, N), d - 1, replace=False)
        cur = int(batch_cost(MT, inv, S[None, :])[0])
        since = 0
        while time.monotonic() < deadline:
            if cur < bestc:
                bestc, best = cur, S.copy()
                since = 0
            if cur == 0 or since > patience:
                break
            i = int(rng.integers(1, d))
            X = propose(MT, inv, S, K, rng)
            X = X[~np.isin(X, np.delete(S, i))]
            if X.size == 0:
                continue
            Cand = np.tile(S, (len(X), 1))
            Cand[:, i] = X
            cs = batch_cost(MT, inv, Cand)
            j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
            delta = int(cs[j]) - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                S[i] = X[j]
                cur = int(cs[j])
            if cur < bestc:
                bestc, best = cur, S.copy()
                since = 0
            else:
                since += 1
        if bestc == 0:
            break
    return best, bestc


# ------------------------------------------------------------------------- graphs

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    g = np.arange(N)
    edges = []
    for s in sorted({int(x) for x in S}):
        for a, b in zip(g, MT[s]):
            edges.append((int(a), int(N + b)))
    return 2 * N, edges


def checked(MT, S, d, D):
    """The Haar graph for S, or None unless lib.is_valid accepts it."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Small always-valid graph for any other (d, D)."""
    cands = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        cands.append(lambda: lib.projective_plane_incidence(d - 1))
    cands.append(lambda: (2 * d, [(i, d + j) for i in range(d) for j in range(d)]))  # K_{d,d}
    for mk in cands:
        try:
            n, edges = mk()
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            pass
    return 2, [(0, 1)]


# ============================================================================ target d10 D5
TARGET = (10, 5)
LO, HI = 2001, 2100
NUM_GROUPS = 6
TIME_FRACTION = 0.72


def metacyclic_specs(lo, hi):
    """('meta', m, k, lam) for Z_m x|_lam Z_k with lo <= m*k <= hi and lam != 1."""
    out = []
    for k in range(2, 11):
        for m in range(-(-lo // k), hi // k + 1):
            if not lo <= m * k <= hi:
                continue
            lams = [lam for lam in range(2, m) if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1][:2]
            for lam in lams:
                out.append(('meta', m, k, lam))
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


FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def run_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline_all = t0 + TIME_FRACTION * time_limit
    rng = np.random.default_rng(seed)

    pool = metacyclic_specs(LO, HI) + [('sl2',), ('heis',), ('agl',)]
    order = rng.permutation(len(pool))
    chosen = [pool[i] for i in order[:NUM_GROUPS]]

    for idx, spec in enumerate(chosen):
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) / (len(chosen) - idx)
        try:
            MT, inv = make_builder(spec)()
            S, c = anneal(MT, inv, d, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g

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
    return run_target(d, D, seed, time_limit)
