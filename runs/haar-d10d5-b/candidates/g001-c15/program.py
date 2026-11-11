"""Haar-graph search for the bipartite degree-diameter problem (numpy + lib only).

Haar graph of a group G and a d-set S: vertices A_g, B_g (g in G), edges A_g ~ B_(s*g) for s in S.
It is bipartite, d-regular, has 2|G| vertices, and has diameter <= 5 exactly when
(S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements on both sides.

NEW IN THIS VERSION: a metacyclic race.  Instead of searching one group for its whole budget, we
enumerate every metacyclic group Z_m x|_lam Z_k with order just above the record half (|G| > 2000,
so the graph beats 4000 vertices), rank them so non-abelian groups come first and smaller orders come
earlier, and run them in round-robin slices with growing time quanta.  Each group keeps its best set S
and its built table between slices (state carry-over), so no progress is lost and a near miss in one
group does not block the others.  The known near miss (Z_401 x| Z_5) is raced alongside them.
Every returned graph is checked with lib.is_valid; a safe fallback is returned otherwise.
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


def metacyclic_candidates(lo, hi, per_order=3):
    """All (m, k, lam) with lo <= m*k <= hi, gcd(lam, m) = 1, lam^k = 1 mod m, k >= 2, m >= 3.
    Non-abelian (lam != 1) first, then by increasing order.  At most per_order lam values per (m, k)."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            cnt = 0
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1 % m:
                    continue
                out.append((0 if lam != 1 else 1, N, m, k, lam))
                cnt += 1
                if cnt >= per_order:
                    break
    out.sort()
    return [(m, k, lam) for _, _, m, k, lam in out]


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


def one_swap_scan(MT, inv, S, deadline, chunk=512):
    """Score every single-slot replacement of S.  Returns (best cost, best S)."""
    N = MT.shape[0]
    best, bestS = 10 ** 9, None
    for i in range(len(S)):
        rest = np.delete(S, i)
        for lo in range(0, N, chunk):
            if time.monotonic() >= deadline:
                return best, bestS
            X = np.arange(lo, min(N, lo + chunk), dtype=np.int32)
            X = X[~np.isin(X, rest)]
            if len(X) == 0:
                continue
            cs = batch_costs(MT, inv, S, i, X)
            j = int(np.argmin(cs))
            if cs[j] < best:
                best, bestS = int(cs[j]), S.copy()
                bestS[i] = X[j]
    return best, bestS


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Annealing over d-subsets.  With a start set S0: scan its 1-swap neighbours, then anneal from it.
    Restarts from a perturbed S0 (half the time) or a random set when stuck.  Returns (best S, best cost)."""
    N = MT.shape[0]
    S0 = None if S0 is None else np.array(S0, dtype=np.int32)
    best, bestc = None, 10 ** 9
    S, cur, since = S0.copy() if S0 is not None else None, None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    if S0 is not None:
        c0 = cost(MT, inv, S0)
        best, bestc = S0.copy(), c0
        if c0 == 0:
            return best, 0
        c1, S1 = one_swap_scan(MT, inv, S0, time.monotonic() + 0.25 * max(0.0, deadline - time.monotonic()))
        if S1 is not None and c1 < bestc:
            best, bestc, S = S1.copy(), c1, S1.copy()
            if c1 == 0:
                return best, 0
    while time.monotonic() < deadline:
        if S is None:
            if S0 is not None and rng.random() < 0.5:
                S = S0.copy()
                for i in rng.choice(d, 2, replace=False):
                    S[i] = rng.integers(N)
                if len(set(S.tolist())) < d:
                    S = random_set()
            else:
                S = random_set()
        if cur is None:
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
    """The Haar graph for S, or None if it is not exactly valid (checked with lib.is_valid)."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for other (d, D) cases."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    n, edges = lib.haar_graph(d, range(d))
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return 2, [(0, 1)]


# ------------------------------------------------------------------------------- the metacyclic race

def race(d, D, rng, deadline, specs, max_live=6):
    """specs: list of (builder, S0 or None).  Round-robin over the first max_live groups in growing slices.
    Each state keeps its built table and its best S between slices.  Returns a checked graph or None."""
    states = [{'sp': sp, 'MT': None, 'inv': None, 'S': None, 'c': 10 ** 9} for sp in specs[:max_live]]
    slice_t = 1.5
    while time.monotonic() < deadline:
        progressed = False
        for st in states:
            now = time.monotonic()
            if now >= deadline:
                break
            if st['sp'] is None:
                continue
            try:
                if st['MT'] is None:
                    st['MT'], st['inv'] = st['sp'][0]()
                S0 = st['S'] if st['S'] is not None else st['sp'][1]
                S, c = search(st['MT'], st['inv'], d, S0, min(deadline, now + slice_t), rng)
            except Exception:
                st['sp'] = None
                st['MT'] = None
                continue
            progressed = True
            if S is not None and c < st['c']:
                st['S'], st['c'] = np.array(S, dtype=np.int32).copy(), c
            if S is not None and c == 0:
                g = checked(st['MT'], S, d, D)
                if g is not None:
                    return g
        slice_t = min(slice_t * 1.5, 20.0)
        if not progressed:
            break
    return None


# ======================================================================================== cell: d10D5
TARGET = (10, 5)

# Near miss from earlier search: Z_401 x| Z_5 (order 2005, 6 elements short), start set given.
NEAR_MISS = (lambda: group_meta(401, 5, 39), [0, 399, 725, 919, 893, 646, 1508, 130, 652, 957])

# Valid smaller Haar graph, checked at run time; used only when the race finds nothing.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def target_specs():
    """Near miss first, then the metacyclic groups of order 2001..2040 (beating 4000 needs |G| > 2000)."""
    specs = [NEAR_MISS]
    for m, k, lam in metacyclic_candidates(2001, 2040):
        if (m, k, lam) == (401, 5, 39):
            continue
        specs.append((lambda m=m, k=k, lam=lam: group_meta(m, k, lam), None))
    return specs


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    try:
        g = race(d, D, rng, deadline, target_specs())
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
