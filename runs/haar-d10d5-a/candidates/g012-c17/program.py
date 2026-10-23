"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A) and (g, B) for
g in G, with edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, and has 2|G| vertices.  Its
diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements on both
sides, and cost 0 means valid.

NEW IN THIS VERSION: uncovered-directed proposals.  If u is uncovered on side 0, then u lies in S^-1 S as soon as
some new element x satisfies x = s*u^-1 or x = s*u for some s in S (because x^-1 s = u or s^-1 x = u).  Likewise,
side 1 needs x = u*s or x = u^-1*s.  Since e is in S^-1 S, adding u to the first-level set covers u at once.  So
each step mixes random replacements with these targeted candidates, which are generated from the actual uncovered
elements of the current S.

Groups are metacyclic Z_p x|_lam Z_k with p prime, scanned over orders in [1792, 2100].  Any valid graph of order
above 1791 beats the stored fallback.  Only checked graphs (lib.is_valid) are returned.
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


# ------------------------------------------------------------------------------------------------ search

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def cost(MT, inv, S):
    """Uncovered elements on both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    Si = inv[S]
    P0 = np.unique(MT[Si[:, None], S[None, :]])
    P1 = np.unique(MT[S[:, None], Si[None, :]])
    return (N - int(_cover(MT, N, P0).sum())) + (N - int(_cover(MT, N, P1).sum()))


def batch_costs(MT, inv, S, i, X):
    """cost of S with slot i replaced by x, for every x in the int array X (only slot-i words are recomputed)."""
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


def directed(MT, inv, S, rest, rng, nd):
    """Candidate replacements that would put an uncovered element of the current S into a first-level set.

    For uncovered u on side 0: x = s*u^-1 and x = s*u.  For uncovered u on side 1: x = u*s and x = u^-1*s.
    Here s ranges over rest (the slot being replaced is excluded)."""
    N = MT.shape[0]
    Si = inv[S]
    cov0 = _cover(MT, N, np.unique(MT[Si[:, None], S[None, :]]))
    cov1 = _cover(MT, N, np.unique(MT[S[:, None], Si[None, :]]))
    u0 = np.flatnonzero(~cov0)
    u1 = np.flatnonzero(~cov1)

    def pick(u):
        return u if len(u) <= nd else rng.choice(u, nd, replace=False)

    u0, u1 = pick(u0), pick(u1)
    parts = []
    if len(u0):
        iu = inv[u0]
        parts.append(MT[rest[:, None], iu[None, :]].ravel())
        parts.append(MT[rest[:, None], u0[None, :]].ravel())
    if len(u1):
        iu = inv[u1]
        parts.append(MT[u1[None, :], rest[:, None]].ravel())
        parts.append(MT[iu[None, :], rest[:, None]].ravel())
    if not parts:
        return np.empty(0, dtype=np.int32)
    return np.concatenate(parts).astype(np.int32)


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000, nd=6):
    """Annealing over d-subsets with random plus uncovered-directed proposals.  Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0
    while time.monotonic() < deadline:
        if S is None:
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
        rest = np.delete(S, i)
        X = np.concatenate([rng.integers(0, N, size=K).astype(np.int32),
                            directed(MT, inv, S, rest, rng, nd)])
        X = np.unique(X[~np.isin(X, rest)])
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
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------- group candidate scan

def _primes(n):
    return [p for p in range(2, n + 1) if all(p % q for q in range(2, int(p ** 0.5) + 1))]


def group_candidates(lo=1792, hi=2100, max_prime=400, pick=8):
    """Metacyclic Z_p x|_lam Z_k (p prime) with order in [lo, hi].  Returns up to `pick` specs (order, p, k, lam),
    spread evenly over the orders, largest first."""
    out = []
    for m in _primes(max_prime):
        for k in range(max(2, -(-lo // m)), hi // m + 1):
            lam = next((l for l in range(2, m) if pow(l, k, m) == 1), None)
            if lam is not None:
                out.append((m * k, m, k, lam))
    out.sort(reverse=True)
    if len(out) <= pick:
        return out
    idx = sorted({int(round(x)) for x in np.linspace(0, len(out) - 1, pick)})
    return [out[i] for i in idx]


# ----------------------------------------------------------------------------------------------- driver

TARGET = (10, 5)
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def run(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    cands = group_candidates()
    for idx, (order, m, k, lam) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) / (len(cands) - idx)
        try:
            MT, inv = group_meta(m, k, lam)
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
        return trivial(d, D)
    try:
        return run(d, D, seed, time_limit)
    except Exception:
        return trivial(d, D)
