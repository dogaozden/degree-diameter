"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A) and (g, B), g in G,
and edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, has 2|G| vertices, and its diameter is at
most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements of those two word sets;
cost 0 means valid.

WHAT CHANGED.  The parent searched a short hand-picked list of groups.  This version enumerates every faithful
metacyclic group Z_m x| Z_k (m*k in [2000, 2100], lam of exact order k mod m) and adds the SL(2,7), Heis(7) and AGL
groups.  It runs round-robin annealing over all of them in short slices, so many groups get a quick look instead of
a few getting long runs.  This is a bet on the family, not a guaranteed gain.  Every cost-0 result is checked with
lib.is_valid before it is returned.  If nothing reaches cost 0 in the budget, the parent's valid order-1791 Haar
graph is returned after its own check, and a trivial graph is the last resort.
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
    """GF(q) x| C_k, maps t -> a*t + b with a in the order-k subgroup of GF(q)^* (default AGL(1, q))."""
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


def search(MT, inv, d, rng, deadline, K=24, temp=0.45, patience=1500):
    """Simulated annealing over d-subsets of the group from random starts, restarting when stuck.
    Returns (S, cost); cost 0 means a valid diameter-5 Haar graph."""
    N = MT.shape[0]

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    S = random_set()
    cur = cost(MT, inv, S)
    best, bestc = S.copy(), cur
    if cur == 0:
        return best, 0
    since = 0
    while time.monotonic() < deadline:
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
            S = random_set()
            cur = cost(MT, inv, S)
            since = 0
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


# ======================================================================================== target d10D5

TARGET = (10, 5)
ORDER_LO, ORDER_HI = 2000, 2100     # group orders that give 2|G| >= record (4000)
MAX_METACYCLIC = 12                 # how many enumerated groups to try
SLICE = 3.0                         # seconds per group per round
BUDGET_FRACTION = 0.72              # leave margin under time_limit

# Parent's valid smaller Haar graph (order 1791, 3582 vertices), checked at run time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def metacyclic_specs(lo, hi):
    """(order, m, k, lam) for faithful Z_m x|_lam Z_k with lo <= m*k <= hi and lam of exact order k mod m."""
    specs = []
    for k in range(2, 64):
        for m in range(max(2, lo // k), hi // k + 2):
            order = m * k
            if order < lo or order > hi:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1 % m:
                    continue
                # exact order of lam must be k (faithful action, so the group is genuinely non-abelian)
                ord_lam = next(j for j in range(1, k + 1) if pow(lam, j, m) == 1 % m)
                if ord_lam == k:
                    specs.append((order, m, k, lam))
    specs.sort()
    return specs


def target_builders():
    """Group builders to rotate through: enumerated metacyclic groups first, then the non-metacyclic families."""
    builders = []
    seen = set()
    for order, m, k, lam in metacyclic_specs(ORDER_LO, ORDER_HI):
        key = (m, k, lam)
        if key in seen:
            continue
        seen.add(key)
        builders.append((f"Z{m} x| Z{k} lam={lam}", lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
        if len(builders) >= MAX_METACYCLIC:
            break
    builders.append(("SL(2,7) x Z6", lambda: group_times_cyclic(group_sl2(7), 6)))
    builders.append(("Heis(7) x Z6", lambda: group_times_cyclic(group_heis(7), 6)))
    builders.append(("AGL(1,13) x Z13", lambda: group_times_cyclic(group_agl(13), 13)))
    builders.append(("AGL(1,16) x Z9", lambda: group_times_cyclic(group_agl(16), 9)))
    return builders


def solve_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline_all = t0 + BUDGET_FRACTION * time_limit
    rng = np.random.default_rng(seed)
    builders = target_builders()

    # Round-robin over the group builders, short slices each, until the budget is spent.
    while builders and time.monotonic() < deadline_all - 1.0:
        for name, mk in builders:
            now = time.monotonic()
            if now >= deadline_all - 1.0:
                break
            end = min(deadline_all, now + SLICE)
            try:
                MT, inv = mk()
                S, c = search(MT, inv, d, rng, end)
            except Exception:
                continue
            if c == 0:
                g = checked(MT, S, d, D)
                if g is not None:
                    return g

    # Safe fallback: the parent's valid order-1791 Haar graph.
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
        return solve_target(d, D, seed, time_limit)
    except Exception:
        return trivial(d, D)
