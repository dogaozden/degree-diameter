"""Haar-graph portfolio for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A), (g, B) for g in G
and edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, has 2|G| vertices, and its diameter is at
most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  cost(S) counts uncovered elements on both sides; cost 0 = valid.

WHAT CHANGED.  The previous plan spent its budget on four large groups.  This version searches a portfolio of
NON-cyclic-friendly group families whose orders lie in [1800, 2000], i.e. just above the order 1791 of the
known-valid fallback (which gives 3582 vertices).  Families: AGL(1,q) and AGL(1,q) x Z_k, SL(2,5) x Z_k,
Heisenberg(3) and Heisenberg(5) x Z_k, and metacyclic Z_m x| Z_k.  Each candidate is annealed for a short
slice, slices grow round by round, and any group reaching cost 0 is built and checked with lib.is_valid.
Once a valid graph is found, only strictly larger groups are tried.  If nothing beats the fallback, the
checked fallback (3582 vertices) is returned, so every case still returns a valid graph.
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


def one_swap_scan(MT, inv, S, deadline, chunk=512):
    """Score EVERY single-slot replacement of S (all slots x all group elements).  Returns (best cost, best S)."""
    N = MT.shape[0]
    best, bestS = 10 ** 9, None
    for i in range(len(S)):
        rest = np.delete(S, i)
        for lo in range(0, N, chunk):
            if time.monotonic() >= deadline:
                return best, bestS
            X = np.arange(lo, min(N, lo + chunk), dtype=np.int32)
            X = X[~np.isin(X, rest)]
            cs = batch_costs(MT, inv, S, i, X)
            j = int(np.argmin(cs))
            if cs[j] < best:
                best, bestS = int(cs[j]), S.copy()
                bestS[i] = X[j]
    return best, bestS


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Local search over d-subsets of the group.  With a start set S0: scan all its 1-swap neighbours first, then
    anneal from it, and restart from a perturbed S0 (half the time) or a random set when stuck.
    Returns (best S, best cost)."""
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
        c1, S1 = one_swap_scan(MT, inv, S0, time.monotonic() + 0.25 * (deadline - time.monotonic()))
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
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ======================================================================================== cell: d10D5
TARGET = (10, 5)      # the (d, D) this plan is for; every other case gets a small always-valid graph

# Any valid Haar graph built from a group of order N > 1791 yields 2N > 3582 vertices.
PARENT_ORDER = 1791

# Known-valid fallback (order 1791, 3582 vertices), checked at run time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def _prod(make_group, k):
    """Builder for make_group() x Z_k."""
    return lambda: group_times_cyclic(make_group(), k)


def _table_candidates():
    """(order, name, builder) for non-cyclic-friendly groups with order in [1800, 2016]."""
    P = _prod
    return [
        (1806, "AGL(1,43)", lambda: group_agl(43)),
        (1806, "AGL(1,7) x Z43", P(lambda: group_agl(7), 43)),
        (1800, "AGL(1,5) x Z90", P(lambda: group_agl(5), 90)),
        (1800, "AGL(1,9) x Z25", P(lambda: group_agl(9), 25)),
        (1800, "SL(2,5) x Z15", P(lambda: group_sl2(5), 15)),
        (1809, "Heis(3) x Z67", P(lambda: group_heis(3), 67)),
        (1840, "AGL(1,5) x Z92", P(lambda: group_agl(5), 92)),
        (1848, "AGL(1,7) x Z44", P(lambda: group_agl(7), 44)),
        (1848, "AGL(1,8) x Z33", P(lambda: group_agl(8), 33)),
        (1870, "AGL(1,11) x Z17", P(lambda: group_agl(11), 17)),
        (1872, "AGL(1,9) x Z26", P(lambda: group_agl(9), 26)),
        (1875, "Heis(5) x Z15", P(lambda: group_heis(5), 15)),
        (1890, "AGL(1,7) x Z45", P(lambda: group_agl(7), 45)),
        (1890, "Heis(3) x Z70", P(lambda: group_heis(3), 70)),
        (1920, "SL(2,5) x Z16", P(lambda: group_sl2(5), 16)),
        (1920, "AGL(1,16) x Z8", P(lambda: group_agl(16), 8)),
        (2000, "Heis(5) x Z16", P(lambda: group_heis(5), 16)),
        (2016, "SL(2,7) x Z6", P(lambda: group_sl2(7), 6)),
    ]


def _metacyclic_candidates():
    """(order, name, builder) for metacyclic groups Z_m x|_lam Z_k with order N in [1800, 2000]."""
    out = []
    for N in (1800, 1848, 1872, 1920, 1960, 2000):
        for k in (3, 4, 6, 8, 9, 10, 12, 15, 16):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lam = None
            for cand in list(range(2, min(m, 300))) + [m - 1]:
                if math.gcd(cand, m) == 1 and cand % m != 1 and pow(cand, k, m) == 1 % m:
                    lam = cand
                    break
            if lam is None:
                continue
            out.append((N, f"Z{m} x| Z{k} lam={lam}",
                        (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
    return out


def _candidates():
    cands = _table_candidates() + _metacyclic_candidates()
    cands = [c for c in cands if c[0] > PARENT_ORDER]
    cands.sort(key=lambda t: t[0])   # smallest orders first: most likely to be valid
    return cands


def run_portfolio(d, D, seed, time_limit, cands, fallback):
    t0 = time.monotonic()
    deadline = t0 + min(0.80 * time_limit, time_limit - 6.0)
    rng = np.random.default_rng(seed)
    usable = max(1.0, deadline - t0)
    base = max(0.5, usable / (2.0 * max(1, len(cands))))

    best = None
    best_order = PARENT_ORDER
    dead = set()
    r = 0
    while time.monotonic() < deadline:
        progress = False
        for idx, (order, name, builder) in enumerate(cands):
            if idx in dead or order <= best_order:
                continue
            if time.monotonic() >= deadline:
                break
            try:
                MT, inv = builder()
            except Exception:
                dead.add(idx)
                continue
            end = min(deadline, time.monotonic() + base * (2.0 ** r))
            try:
                S, c = search(MT, inv, d, None, end, rng)
            except Exception:
                dead.add(idx)
                continue
            progress = True
            if S is not None and c == 0:
                g = checked(MT, S, d, D)
                if g is not None:
                    best = g
                    best_order = order
        r += 1
        if not progress:
            break

    if best is not None:
        return best
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
        return run_portfolio(d, D, seed, time_limit, _candidates(), FALLBACK)
    except Exception:
        return trivial(d, D)
