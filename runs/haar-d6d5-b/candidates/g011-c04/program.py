"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

Change in this version: instead of annealing a few hand-picked groups in fixed time slices, the target
case now searches a broad family of groups with orders 336..420 (metacyclic Z_m x| Z_k, Heisenberg,
SL(2,p) x Z_k, AGL(1,q) subgroups and products with Z_k). Groups are tried in ascending order of size,
round-robin, and any valid Haar graph larger than the current best replaces it. A checked smaller Haar
graph (order 330) is in hand from the start, so every case still returns a valid graph.

Haar graph: vertices (g, A) and (g, B), edges (g, A) ~ (s*g, B) for s in S with |S| = d. It has 2|G|
vertices, is bipartite and d-regular, and has diameter at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.
Annealing minimises the number of uncovered group elements on both sides; cost 0 means valid.
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
    """Table of a group given as an (N, c) integer coordinate array (element 0 must be the identity)
    and a vectorised product mulfun(X, Y) of two (..., c) arrays."""
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
    """Heisenberg group mod p (upper unitriangular 3x3), order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)   # (0,0,0) is first

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, matrices (a, b, c, d), order p(p^2-1)."""
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
    """GF(q) x| C_k: the maps t -> a*t + b on GF(q) with a in the subgroup of order k of GF(q)^* (default k = q-1,
    that is AGL(1, q)).  q a prime power (uses lib.GF).  The product is (b1, a1)(b2, a2) = (b1 + a1*b2, a1*a2)."""
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


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Simulated-annealing style local search over d-subsets of the group, with restarts.
    Returns (best S, best cost); cost 0 means a valid Haar graph."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

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
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------- broad candidate family

def candidate_specs(rng, lo=336, hi=420):
    """(order, builder) for many groups of order lo..hi, sorted by order (ties shuffled)."""
    specs = []
    # Metacyclic Z_m x|_lam Z_k with lam nontrivial.
    for m in range(3, hi + 1):
        for k in range(2, hi // m + 1):
            n = m * k
            if not lo <= n <= hi:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1 % m:
                    continue
                specs.append((n, lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
    # Base groups, optionally times Z_k.
    bases = [(27, lambda: group_heis(3)), (24, lambda: group_sl2(3)),
             (120, lambda: group_sl2(5)), (343, lambda: group_heis(7))]
    for q in (4, 5, 7, 8, 9, 11, 13):
        bases.append((q * (q - 1), lambda q=q: group_agl(q)))
    # AGL(1,q) subgroups of order q*k, k | q-1.
    for q in (7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32):
        for k in range(2, q):
            if (q - 1) % k == 0 and lo <= q * k <= hi:
                specs.append((q * k, lambda q=q, k=k: group_agl(q, k)))
    for bn, bf in bases:
        for k in range(1, hi // bn + 1):
            n = bn * k
            if lo <= n <= hi:
                if k == 1:
                    specs.append((n, lambda bf=bf: bf()))
                else:
                    specs.append((n, lambda bf=bf, k=k: group_times_cyclic(bf(), k)))
    keys = rng.random(len(specs))
    order = sorted(range(len(specs)), key=lambda i: (specs[i][0], keys[i]))
    return [specs[i] for i in order]


# ------------------------------------------------------------------------------------- the run loop

POOL = 8        # how many of the smallest-order untried groups are searched round-robin
SLICE = 4.0     # seconds per group per round, at most


def run2(d, D, seed, time_limit, fallback):
    """Round-robin search over the group family; keeps the largest checked valid Haar graph."""
    t0 = time.monotonic()
    deadline = t0 + max(1.0, 0.78 * time_limit - 1.0)
    rng = np.random.default_rng(seed)

    best, best_order = None, 0
    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            best, best_order = g, g[0] // 2
    except Exception:
        pass

    try:
        specs = candidate_specs(rng)
    except Exception:
        specs = []

    cache, dead = {}, set()
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0.3:
            break
        pool = [i for i, (o, _) in enumerate(specs) if o > best_order and i not in dead][:POOL]
        if not pool:
            break
        slice_t = min(SLICE, remaining / len(pool))
        for i in pool:
            if specs[i][0] <= best_order:
                continue
            now = time.monotonic()
            if deadline - now <= 0.3:
                break
            end = min(deadline, now + slice_t)
            if i not in cache:
                try:
                    cache[i] = specs[i][1]()
                except Exception:
                    dead.add(i)
                    continue
            MT, inv = cache[i]
            try:
                S, c = search(MT, inv, d, end, rng)
            except Exception:
                dead.add(i)
                continue
            if S is not None and c == 0:
                g = checked(MT, S, d, D)
                if g is not None and g[0] // 2 > best_order:
                    best, best_order = g, g[0] // 2
        cache = {i: v for i, v in cache.items() if i in pool}

    return best if best is not None else trivial(d, D)


# ============================================================================ cell: d6D5 (target)
TARGET = (6, 5)

# Valid smaller Haar graph (order 330), checked at run time; the floor for this case.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        return run2(d, D, seed, time_limit, FALLBACK)
    except Exception:
        return trivial(d, D)
