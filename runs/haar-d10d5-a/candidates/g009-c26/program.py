"""Combined Haar-graph search for the d=10, D=5 target (numpy only).

A Haar graph on a group G with connection set S (|S| = d) has 2|G| vertices and is d-regular and bipartite.
Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G. The search anneals S to cost 0 over
non-abelian metacyclic groups Z_m x|_lam Z_k. Orders above 2000 are swept first, since they beat the
record of 4000. Orders 1792..2000 come second, since they still beat the stored fallback of 3582.
Every returned graph is checked with lib.is_valid.
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
    P0 = MT[Si[:, None], S[None, :]].ravel()
    P1 = MT[S[:, None], Si[None, :]].ravel()
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in (P0, P1))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by x, for every x in X (only slot-i words are recomputed)."""
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


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Simulated-annealing style local search over d-subsets containing the identity.
    Returns (best S, best cost); cost 0 means a valid Haar graph."""
    N = MT.shape[0]

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0
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
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ======================================================================================== cell: d10D5
TARGET = (10, 5)

# Sweep high orders first (beat the record 4000 needs |G| >= 2001), then the lower band (beats the fallback 3582).
BANDS = [(2001, 2100), (1792, 2000)]
SLICE = 4.0           # seconds of annealing per candidate group

# Valid smaller Haar graph (|G| = 1791), checked at run time; returned only if nothing better is found.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def metacyclic_candidates(lo, hi):
    """All (N, m, k, lam) with N = m*k in [lo, hi], k >= 2, m >= 3, and lam a non-trivial unit mod m with
    lam^k = 1 mod m, so Z_m x|_lam Z_k is a non-abelian group of order N."""
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
                out.append((N, m, k, lam))
    return out


def run_meta(d, D, seed, time_limit):
    """Annealing over metacyclic groups, band by band. Returns the first checked valid Haar graph, else the fallback."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.85 * time_limit
    rng = np.random.default_rng(seed)

    order = []
    for lo, hi in BANDS:
        keyed = {}
        for c in metacyclic_candidates(lo, hi):
            keyed.setdefault(c[0], []).append(c)
        for N in sorted(keyed):
            grp = keyed[N]
            rng.shuffle(grp)
            order.extend(grp)

    idx = 0
    while order:
        now = time.monotonic()
        remaining = deadline_all - now
        if remaining < 0.5:
            break
        _, m, k, lam = order[idx % len(order)]
        idx += 1
        slice_end = now + min(SLICE, remaining)
        try:
            MT, inv = group_meta(m, k, lam)
            S, c = search(MT, inv, d, slice_end, rng)
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
    return run_meta(d, D, seed, time_limit)
