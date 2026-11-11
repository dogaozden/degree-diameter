"""Haar-graph search over many groups of order 336..370 for the bipartite degree-diameter problem (d=6, D=5).

A Haar graph on a group G with connection set S (|S| = d) has vertices (g, A), (g, B) and edges
(g, A) ~ (s*g, B).  It is bipartite, d-regular, has 2|G| vertices, and has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G.  The search scores S by the number of uncovered group elements
(cost 0 = valid) and anneals.  Candidate groups of order above 330 are tried in ascending order,
round-robin with growing time slices.  Every returned graph is checked with lib.is_valid, and the
largest checked graph wins.  The fallback is a valid 660-vertex Haar graph.
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
    """GF(q) x| C_k (default k = q-1, i.e. AGL(1, q)), q a prime power."""
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
    """cost of S with slot i replaced by x, for every x in the int array X."""
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
    """Annealing from random d-subsets containing the identity, with restarts when stuck.
    Returns (best S, best cost); S has cost 0 iff it is a valid set."""
    N = MT.shape[0]

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    best, bestc = None, 10 ** 9
    while time.monotonic() < deadline:
        S = random_set()
        cur = cost(MT, inv, S)
        if cur < bestc:
            best, bestc = S.copy(), cur
        if cur == 0:
            return best, 0
        since = 0
        while since <= patience and time.monotonic() < deadline:
            i = int(rng.integers(d))
            X = rng.integers(0, N, size=K).astype(np.int32)
            X = X[~np.isin(X, np.delete(S, i))]
            if len(X) == 0:
                since += 1
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


# ======================================================================================== target d6D5

TARGET = (6, 5)
LO, HI = 336, 370          # candidate group orders; 2*order must beat the 660 parent


def candidate_specs():
    """(order, name, builder) for candidate groups, sorted by order."""
    specs = [
        (336, 'SL(2,7)', lambda: group_sl2(7)),
        (343, 'Heis(7)', lambda: group_heis(7)),
        (351, 'Heis(3) x Z13', lambda: group_times_cyclic(group_heis(3), 13)),
        (360, 'SL(2,5) x Z3', lambda: group_times_cyclic(group_sl2(5), 3)),
        (360, 'AGL(1,9) x Z5', lambda: group_times_cyclic(group_agl(9), 5)),
        (360, 'AGL(1,5) x Z18', lambda: group_times_cyclic(group_agl(5), 18)),
    ]
    for N in range(LO, HI + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lams = [l for l in range(2, m)
                    if math.gcd(l, m) == 1 and pow(l, k, m) == 1 % m]
            for l in lams[:2]:
                specs.append((N, f'Z{m} x| Z{k} lam={l}',
                              (lambda m=m, k=k, l=l: group_meta(m, k, l))))
    specs.sort(key=lambda t: (t[0], t[1]))
    return specs


FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def run_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.75 * time_limit
    rng = np.random.default_rng(seed)
    specs = candidate_specs()
    built = {}
    dead = set()
    best, best_order = None, 0
    slice_s = 1.5

    while time.monotonic() < deadline:
        progressed = False
        for idx, (order, name, builder) in enumerate(specs):
            if time.monotonic() >= deadline:
                break
            if order <= best_order or idx in dead:
                continue
            if idx not in built:
                try:
                    built[idx] = builder()
                except Exception:
                    dead.add(idx)
                    continue
            MT, inv = built[idx]
            end = min(deadline, time.monotonic() + slice_s)
            progressed = True
            try:
                S, c = search(MT, inv, d, end, rng)
            except Exception:
                dead.add(idx)
                continue
            if S is not None and c == 0:
                g = checked(MT, S, d, D)
                if g is not None:
                    best, best_order = g, order
        if not progressed:
            break
        slice_s *= 2

    if best is not None:
        return best
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
    return run_target(d, D, seed, time_limit)
