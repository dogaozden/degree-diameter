"""Haar-graph search for the bipartite degree-diameter problem (numpy only).

A Haar graph on a finite group G with connection set S (|S| = d) has vertices (g, A), (g, B) and edges
(g, A) ~ (s*g, B). It is bipartite, d-regular, has 2|G| vertices, and has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G. cost(S) counts the uncovered group elements; cost 0 means valid.

NEW IN THIS VERSION: a round-robin order sweep. Instead of spending the whole budget on a few large
groups, it sweeps group orders N in [LO, HI]. For each N it lazily lists every metacyclic group
Z_m x|_lam Z_k with m*k = N (plus the Heisenberg and AGL families where they have order N), shuffles them,
and gives each group one short annealing slice per pass. Passes continue until the deadline. After a
success at order N the sweep only considers larger orders, so every success is strictly better.
Every graph returned is checked with lib.is_valid. A precomputed valid Haar graph of order 1791 is checked
first, so the answer is never worse than 3582 vertices at d=10, D=5.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (10, 5)
SLICE = 1.5          # seconds of annealing per (group, pass)
LO, HI = 1792, 2060  # group orders swept (vertices = 2|G|; record 4000 means |G| = 2000)


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
    """Table of a group given as an (N, c) coordinate array (element 0 is the identity) and a vectorised product."""
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
    """GF(q) x| C_k (default k = q-1, i.e. AGL(1, q)), built from lib.GF."""
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
    """Direct product of a table group with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def group_candidates(N, rng):
    """All builders (shuffled) for groups of order N: metacyclic Z_m x| Z_k with nontrivial action,
    plus the known non-metacyclic families of that order."""
    makers = []
    for k in range(2, N // 3 + 1):
        if N % k:
            continue
        m = N // k
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                makers.append(lambda m=m, k=k, lam=lam: group_meta(m, k, lam))
    if N == 2028:
        makers.append(lambda: group_times_cyclic(group_agl(13), 13))
    if N == 2058:
        makers.append(lambda: group_times_cyclic(group_heis(7), 6))
    order = rng.permutation(len(makers))
    return [makers[i] for i in order]


# ------------------------------------------------------------------------------------------------ search

def _cover(MT, N, P):
    """Boolean array of the elements covered by the pair products P."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """(S_i^-1 S_j, S_i S_j^-1) as flat arrays."""
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (0 = valid diameter-5 Haar graph)."""
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
    """Annealing over d-subsets of the group, restarting from random sets when stuck.
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
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    if D >= 2:
        return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]
    return lib.haar_graph(d, range(d))


def sweep(d, D, rng, deadline, lo, hi):
    """Round-robin over group orders N in [lo, hi]: each pass gives every N with candidates one more
    group and a SLICE of annealing. After a success at N only larger orders are tried.
    Returns the largest valid (n, edges) found, or None."""
    best = None
    pools, cur = {}, {}
    while True:
        progressed = False
        for N in range(lo, hi + 1):
            if time.monotonic() >= deadline:
                return best
            if N not in pools:
                pools[N] = group_candidates(N, rng)
                cur[N] = 0
            if cur[N] >= len(pools[N]):
                continue
            make = pools[N][cur[N]]
            cur[N] += 1
            progressed = True
            end = min(deadline, time.monotonic() + SLICE)
            g = None
            try:
                MT, inv = make()
                S, c = search(MT, inv, d, end, rng)
                if S is not None and c == 0:
                    g = checked(MT, S, d, D)
            except Exception:
                g = None
            if g is not None:
                best = g
                lo = N + 1
                break
        if not progressed:
            return best


# FALLBACK: a valid Haar graph of order 1791 (3582 vertices), checked at run time.
FALLBACK_BUILDER = lambda: group_meta(199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.8 * time_limit
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = FALLBACK_BUILDER()
        best = checked(MT, FALLBACK_S, d, D)
    except Exception:
        best = None

    try:
        found = sweep(d, D, rng, deadline, LO, HI)
        if found is not None and (best is None or found[0] > best[0]):
            best = found
    except Exception:
        pass

    return best if best is not None else trivial(d, D)
