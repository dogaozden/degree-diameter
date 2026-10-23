"""Haar-graph search for the bipartite degree-diameter problem, diameter 5 (numpy only).

Haar graph of a group G and a d-set S: vertices (g,A), (g,B); edges (g,A)~(s*g,B).  It is bipartite, d-regular,
with 2|G| vertices, and has diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  cost(S) counts the uncovered
elements on both sides; cost 0 means valid.

NEW IN THIS VERSION (not in the parent):
  1. Targeted moves.  Pick an uncovered element u of one side, write u = w1*w2 with w1 a random pair product
     of the other slots and w2 = w1^-1 u, then solve for a slot value x that makes w2 a pair product containing x.
     These candidates aim straight at the holes; they are mixed with random candidates and scored exactly.
  2. Automatic group portfolio.  candidate_meta enumerates metacyclic groups Z_m x| Z_k of order in a window
     just above record/2 and round-robins short annealing slices over them, carrying each group's best set forward.

Every returned graph is checked with lib.is_valid; otherwise a smaller valid Haar graph or a trivial graph is used.
"""
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
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
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


def candidate_meta(lo, hi, kmin=3, kmax=12, limit=8):
    """Metacyclic groups Z_m x|_lam Z_k (lam != 1, lam^k = 1 mod m) with order in [lo, hi], smallest order first."""
    out = []
    for k in range(kmin, kmax + 1):
        for m in range(lo // k, hi // k + 2):
            N = m * k
            if N < lo or N > hi:
                continue
            for lam in range(2, m):
                if pow(lam, k, m) == 1 % m:
                    out.append((N, -k, m, lam))
    out.sort()
    return [(m, -nk, lam) for N, nk, m, lam in out[:limit]]


# ------------------------------------------------------------------------------------ coverage and cost

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def covers(MT, inv, S):
    """(side-0 coverage, side-1 coverage, total uncovered) for the set S."""
    N = MT.shape[0]
    Si = inv[S]
    P0 = np.unique(MT[Si[:, None], S[None, :]])
    P1 = np.unique(MT[S[:, None], Si[None, :]])
    c0 = _cover(MT, N, P0)
    c1 = _cover(MT, N, P1)
    return c0, c1, (N - int(c0.sum())) + (N - int(c1.sum()))


def cost(MT, inv, S):
    """Uncovered elements on both sides (0 = valid diameter-5 Haar graph)."""
    return covers(MT, inv, S)[2]


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X (only the words involving slot i are recomputed)."""
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


# ------------------------------------------------------------------------- NEW: targeted candidates

def targeted(MT, inv, S, c0, c1, rng, M):
    """Candidate replacement values that would cover a random uncovered element.

    Pick side and uncovered u, pair products w1 = a^-1 b (or a b^-1) of random slots a, b, and set
    w2 = w1^-1 u.  Solve for x in the pair product w2 = x^-1 y, y^-1 x (side 0) or x y^-1, y x^-1 (side 1)
    for every slot value y.  Returns an int64 array of candidates (possibly empty)."""
    side = int(rng.integers(2))
    cov = c0 if side == 0 else c1
    unc = np.flatnonzero(~cov)
    if unc.size == 0:
        return np.empty(0, dtype=np.int64)
    d = len(S)
    u = unc[rng.integers(unc.size, size=M)]
    a = S[rng.integers(d, size=M)]
    b = S[rng.integers(d, size=M)]
    w1 = MT[inv[a], b] if side == 0 else MT[a, inv[b]]
    w2 = MT[inv[w1], u]
    iw2 = inv[w2]
    y = S[None, :]
    if side == 0:
        C = [MT[y, iw2[:, None]], MT[y, w2[:, None]]]
    else:
        C = [MT[w2[:, None], y], MT[iw2[:, None], y]]
    return np.concatenate([c.ravel() for c in C]).astype(np.int64)


# ------------------------------------------------------------------------------------------- search

def anneal(MT, inv, d, S, deadline, rng, K=64, temp=0.45, patience=2500):
    """Annealing on d-subsets with targeted + random candidate moves.  Returns (best S, best cost)."""
    N = MT.shape[0]

    def rand_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    S = rand_set() if S is None else np.array(S, dtype=np.int32)
    cur = cost(MT, inv, S)
    best, bestc = S.copy(), cur
    since = 0
    while bestc > 0 and time.monotonic() < deadline:
        c0, c1, _ = covers(MT, inv, S)
        i = int(rng.integers(d))
        rest = np.delete(S, i)
        X = np.concatenate([targeted(MT, inv, S, c0, c1, rng, 8),
                            rng.integers(0, N, size=K // 2).astype(np.int64)])
        X = np.unique(X)
        X = X[~np.isin(X, rest)]
        if X.size == 0:
            continue
        if X.size > K:
            X = rng.choice(X, K, replace=False)
        X = X.astype(np.int32)
        cs = batch_costs(MT, inv, S, i, X)
        j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
        delta = int(cs[j]) - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S[i] = X[j]
            cur = int(cs[j])
            if cur < bestc:
                best, bestc, since = S.copy(), cur, 0
                continue
        since += 1
        if since > patience:
            if rng.random() < 0.5:
                S = best.copy()
                for t in rng.choice(d, 3, replace=False):
                    S[t] = rng.integers(N)
                if len(set(S.tolist())) < d:
                    S = rand_set()
            else:
                S = rand_set()
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = S.copy(), cur
    return best, bestc


# --------------------------------------------------------------------------------------- the graph

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g,A) ~ (s*g,B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if lib.is_valid rejects it."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for other (d, D) cases."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------------------ build

TARGET = (10, 5)
NEAR = (401, 5, 39)                      # order 2005, near miss (6 uncovered)
NEAR_S0 = [0, 399, 725, 919, 893, 646, 1508, 130, 652, 957]
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])
SLICE = 3.0                              # seconds per group visit in the round-robin


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    end_all = t0 + 0.75 * time_limit
    rng = np.random.default_rng(seed)

    params = [NEAR, NEAR] + candidate_meta(2001, 2080, limit=8)
    states = [np.array(NEAR_S0, dtype=np.int32), np.array(NEAR_S0, dtype=np.int32)]
    states += [None] * (len(params) - 2)

    while time.monotonic() < end_all - 0.5:
        for e, (m, k, lam) in enumerate(params):
            now = time.monotonic()
            if now >= end_all - 0.5:
                break
            slice_end = min(end_all, now + SLICE)
            try:
                MT, inv = group_meta(m, k, lam)
                S, c = anneal(MT, inv, d, states[e], slice_end, rng)
            except Exception:
                continue
            states[e] = S
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
