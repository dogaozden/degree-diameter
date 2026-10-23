"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

CHANGE FROM PARENT: instead of a few hand-picked groups, the target case sweeps a broad pool of
groups with order just above 2000 (the record 4000 = 2 * 2000 needs order > 2000 to beat it).
The pool holds metacyclic groups Z_m x|_lam Z_k, times cyclic factors Z_j, plus the named
non-abelian families. Groups are annealed in round-robin with doubling time slices, so cheap
early checks cover many groups before any one gets a long run. Only a graph that passes
lib.is_valid is returned. If nothing reaches cost 0, the valid order-1791 Haar graph
(3582 vertices) is returned as the fallback.

THEORY.  For a group G and a set S of size d, the Haar graph has vertices (g, A), (g, B) and edges
(g, A) ~ (s*g, B).  It is bipartite, d-regular, with 2|G| vertices.  Its diameter is at most 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements; cost 0 means valid.
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
    """GF(q) x| C_k: maps t -> a*t + b with a in the subgroup of order k of GF(q)^* (default AGL(1, q))."""
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
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    Si = inv[S]
    P0 = np.unique(MT[Si[:, None], S[None, :]].ravel())
    P1 = np.unique(MT[S[:, None], Si[None, :]].ravel())
    return (N - int(_cover(MT, N, P0).sum())) + (N - int(_cover(MT, N, P1).sum()))


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
    """Simulated-annealing style local search over d-subsets of the group, with restarts.
    Returns (best S, best cost)."""
    N = MT.shape[0]

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0
    while time.monotonic() < deadline:
        if S is None:
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
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------- candidate group pool

def metacyclic_params(N0, cap=2):
    """Up to cap parameter triples (m, k, lam) with m*k = N0, nonabelian (lam != 1), lam^k = 1 mod m."""
    out = []
    for k in range(2, N0 + 1):
        if N0 % k:
            continue
        m = N0 // k
        if m < 3:
            continue
        for lam in range(2, m):
            if lam == 1 or math.gcd(lam, m) != 1:
                continue
            if pow(lam, k, m) != 1 % m:
                continue
            out.append((m, k, lam))
            if len(out) >= cap:
                return out
    return out


def _meta_builder(m, k, lam, j):
    def b():
        G = group_meta(m, k, lam)
        return group_times_cyclic(G, j) if j > 1 else G
    return b


def _named_builder(fn, *args):
    def b():
        G = fn(*args[:-1]) if len(args) > 1 else fn()
        return G
    return b


def candidate_pool(max_candidates=40):
    """Groups of order 2001..2200, sorted by order, as (order, name, builder)."""
    cands = []
    # Named non-abelian families with order in the window.
    cands.append((2016, 'SL(2,7) x Z6', lambda: group_times_cyclic(group_sl2(7), 6)))
    cands.append((2028, 'AGL(1,13) x Z13', lambda: group_times_cyclic(group_agl(13), 13)))
    cands.append((2058, 'Heis(7) x Z6', lambda: group_times_cyclic(group_heis(7), 6)))
    cands.append((2160, 'AGL(1,16) x Z9', lambda: group_times_cyclic(group_agl(16), 9)))
    for T in range(2001, 2201):
        for j in range(1, T + 1):
            if T % j:
                continue
            N0 = T // j
            if N0 < 6:
                continue
            for (m, k, lam) in metacyclic_params(N0, cap=2):
                cands.append((T, 'Z%d x|%d Z%d x Z%d' % (m, lam, k, j), _meta_builder(m, k, lam, j)))
        if len(cands) >= 4 * max_candidates:
            break
    cands.sort(key=lambda c: (c[0], c[1]))
    return cands[:max_candidates]


# ======================================================================================== target: d10D5

TARGET = (10, 5)

# Valid smaller Haar graph (order 1791, 3582 vertices), used only if the sweep finds nothing.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def run_sweep(d, D, seed, time_limit, cands, fallback):
    """Round-robin over candidate groups with doubling time slices; returns the first checked valid graph."""
    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    if cands:
        slice_t = 0.4
        while time.monotonic() < deadline - 0.05:
            for _, _, builder in cands:
                now = time.monotonic()
                if now >= deadline:
                    break
                end = min(deadline, now + slice_t)
                try:
                    MT, inv = builder()
                    S, c = search(MT, inv, d, end, rng)
                except Exception:
                    continue
                if S is not None and c == 0:
                    g = checked(MT, S, d, D)
                    if g is not None:
                        return g
            slice_t *= 2

    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        cands = candidate_pool()
    except Exception:
        cands = []
    return run_sweep(d, D, seed, time_limit, cands, FALLBACK)
