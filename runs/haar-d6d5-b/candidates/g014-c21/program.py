"""Metacyclic Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

Bold change: instead of Heisenberg / AGL / SL products, the target search uses metacyclic groups
Z_m x|_lam Z_k (non-abelian Frobenius-type families) with orders 336..372. Candidates are tried in
ascending order of order. A success is kept, and only larger orders are tried after it, so the
returned graph is the largest valid one found. Every returned graph is checked with lib.is_valid.
The validated smaller Haar graph (660 vertices) is the fallback, and a small always-valid graph
covers the other cases.

Haar graph theory: vertices (g, A) and (g, B), g in G, edges (g, A) ~ (s*g, B) for s in S, |S| = d.
Diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G. Vertex ids: A-vertex g is g, B-vertex g is N + g.
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


def _mult_order(x, m):
    """Multiplicative order of the unit x mod m."""
    o, y = 1, x % m
    while y != 1:
        y = y * x % m
        o += 1
    return o


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
    """Uncovered elements, both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by x, for every x in the int array X (only slot-i words are recomputed)."""
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
    """Simulated-annealing style local search over d-subsets of the group, with restarts when stuck.
    Returns (best S, best cost)."""
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
    """The Haar graph for S, or None if it is not exactly valid (checked with lib.is_valid)."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D): a projective plane, K_{d,d}, or a single edge."""
    options = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        options.append(lib.projective_plane_incidence(d - 1))
    if D >= 2 and d >= 1:
        options.append((2 * d, [(i, d + j) for i in range(d) for j in range(d)]))
    if d >= 1 and D >= 1:
        options.append((2, [(0, 1)]))
    for n, edges in options:
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return 1, []


# ----------------------------------------------------------------------------------------- the plan

def make_candidates(wanted):
    """For each wanted order N, one metacyclic group Z_m x|_lam Z_k of that order (non-abelian, lam != 1).
    Returns [(N, builder, weight)] in ascending N."""
    wanted = set(wanted)
    hi = max(wanted)
    by_n = {}
    for m in range(3, hi):
        for k in range(2, hi // m + 1):
            N = m * k
            if N not in wanted:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1:
                    continue
                by_n.setdefault(N, []).append((_mult_order(lam, m), m, k, lam))
    out = []
    for N in sorted(by_n):
        _, m, k, lam = max(by_n[N])
        out.append((N, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), 1 if N <= 342 else 2))
    return out


def run_plan(d, D, deadline, cands, rng):
    """Try candidates in ascending order. A success is kept, and only larger orders are tried after it.
    Returns the largest valid graph found, or None."""
    best = None
    pending = list(cands)
    while pending:
        if time.monotonic() >= deadline:
            break
        N, builder, w = pending.pop(0)
        if best is not None and N <= best[0]:
            continue
        now = time.monotonic()
        live = [x for x in pending if best is None or x[0] > best[0]]
        total = w + sum(x[2] for x in live)
        end = now + (deadline - now) * w / total
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                best = (N, g)
    return None if best is None else best[1]


TARGET = (6, 5)
WANTED_ORDERS = [336, 340, 342, 343, 344, 345, 348, 350, 352, 357, 360, 368, 372]

# Valid smaller Haar graph (660 vertices), checked at run time; used when the search finds nothing.
FALLBACK_S = [0, 179, 116, 180, 47, 306]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + 0.75 * time_limit
    rng = np.random.default_rng(seed)
    try:
        cands = make_candidates(WANTED_ORDERS)
        g = run_plan(d, D, deadline, cands, rng)
        if g is not None:
            return g
    except Exception:
        pass
    try:
        MT, _ = group_meta(33, 10, 26)
        g = checked(MT, FALLBACK_S, d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
