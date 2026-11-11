"""Haar-graph search for the bipartite degree-diameter problem, diameter 5 (numpy only).

THEORY.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A) and (g, B), g in G,
and edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, has 2|G| vertices, and its diameter is at
most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered group elements on both sides.
Cost 0 means valid.  To beat the record 684 we need |G| >= 343.

NEW IN THIS VERSION.
  1. Targeted moves.  Uncovered elements u (on either side) are turned into proposals.  If a new pair word p
     must satisfy p*q = u for an existing pair product q, the slot value x is solved in closed form.  Half of
     the candidates per step come from these proposals and half are uniform random.  Every proposal is still
     scored exactly by batch_costs, so a bad proposal only costs time.
  2. Group catalogue.  Non-abelian metacyclic groups Z_m x| Z_k with a faithful action of order k, of orders
     344..352, are enumerated and added to the plan.  Heisenberg mod 7 (order 343) and AGL(1,27) x| C_13 and
     Heis(3) x Z_13 (both order 351) are added as well.

Every returned graph is checked with lib.is_valid.  If nothing reaches cost 0, a valid smaller Haar graph
(order 330, 660 vertices) is returned.
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
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
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
    """GF(q) x| C_k: maps t -> a*t + b with a in the order-k subgroup of GF(q)^*.  Product (b1,a1)(b2,a2) = (b1 + a1*b2, a1*a2)."""
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


def metacyclic_catalogue(lo, hi):
    """Metacyclic Z_m x| Z_k of order m*k in [lo, hi] with a faithful action (lam of order exactly k).
    Returns a list of (order, m, k, lam), smallest order first."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(3, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1 % m:
                    continue
                order = next(t for t in range(1, k + 1) if pow(lam, t, m) == 1 % m)
                if order == k:
                    out.append((N, m, k, lam))
    return out


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


def targeted(MT, inv, S, pool, rng, K):
    """NEW: proposals that aim at uncovered elements.  For an uncovered u and an existing pair product q, a new
    pair word p with p*q = u fixes the slot value x in closed form (x = s q u^-1 or s u q^-1 on side 0,
    x = u q^-1 s or q u^-1 s on side 1), with s taken from pool (the slots kept fixed).  Proposals only steer
    the search; every candidate is scored exactly by batch_costs."""
    N = MT.shape[0]
    Si = inv[S]
    P = (np.unique(MT[Si[:, None], S[None, :]]), np.unique(MT[S[:, None], Si[None, :]]))
    cov = (_cover(MT, N, P[0]), _cover(MT, N, P[1]))
    U = (np.nonzero(~cov[0])[0], np.nonzero(~cov[1])[0])
    sides = [sd for sd in (0, 1) if len(U[sd]) > 0]
    if not sides or len(pool) == 0:
        return np.zeros(0, dtype=np.int32)
    per = max(1, K // len(sides))
    out = []
    for sd in sides:
        u = U[sd][rng.integers(0, len(U[sd]), per)]
        q = P[sd][rng.integers(0, len(P[sd]), per)]
        s = pool[rng.integers(0, len(pool), per)]
        form = rng.integers(0, 2, per).astype(bool)
        if sd == 0:
            A = MT[MT[s, q], inv[u]]
            B = MT[MT[s, u], inv[q]]
        else:
            A = MT[MT[u, inv[q]], s]
            B = MT[MT[q, inv[u]], s]
        out.append(np.where(form, A, B))
    return np.concatenate(out).astype(np.int32)


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


def search(MT, inv, d, S0, deadline, rng, K=32, temp=0.45, patience=4000):
    """Local search over d-subsets of the group.  Each step mixes uniform random candidates with targeted
    candidates (NEW).  Restarts from a perturbed S0 or a random set when stuck.  Returns (best S, best cost)."""
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
        rest = np.delete(S, i)
        Xr = rng.integers(0, N, size=K // 2)
        Xt = targeted(MT, inv, S, rest, rng, K - K // 2)
        X = np.unique(np.concatenate([Xr, Xt]).astype(np.int32))
        X = X[~np.isin(X, rest)]
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
    """Small graph for any other (d, D) the evaluator may ask for, always checked."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        g = lib.projective_plane_incidence(d - 1)
    else:
        g = lib.haar_graph(d, range(d))
    if lib.is_valid(g[0], g[1], d, D):
        return g
    return (2, [(0, 1)])


def run(d, D, seed, time_limit, plan, fallback):
    """plan: list of (name, builder, S0 or None, weight); fallback: (builder, S) of a valid smaller graph."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    total_w = sum(w for *_, w in plan)
    for name, builder, S0, w in plan:
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, S0, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g
    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ======================================================================================== cell: d6D5
TARGET = (6, 5)

FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def _meta_b(m, k, lam):
    return lambda: group_meta(m, k, lam)


def _agl_b(q, k):
    return lambda: group_agl(q, k)


def _heis_b(p):
    return lambda: group_heis(p)


def _heis_cyc_b(p, k):
    return lambda: group_times_cyclic(group_heis(p), k)


def _sl2_cyc_b(p, k):
    return lambda: group_times_cyclic(group_sl2(p), k)


def make_plan():
    """Orders 343 (Heis mod 7) and 351 are attempted first, then catalogue metacyclic groups of order 344..352,
    then the parent's near-miss starts (order 351, 355, 360)."""
    plan = [
        ('Heis(7), order 343', _heis_b(7), None, 5),
        ('AGL(1,27) x| C_13, order 351', _agl_b(27, 13), None, 4),
        ('Heis(3) x Z_13, order 351', _heis_cyc_b(3, 13), None, 3),
    ]
    for N, m, k, lam in metacyclic_catalogue(344, 352)[:2]:
        plan.append((f'meta {m}/{k}/{lam}, order {N}', _meta_b(m, k, lam), None, 3))
    plan += [
        ('meta 117/3/16, order 351, 2 short', _meta_b(117, 3, 16), [0, 184, 47, 48, 65, 21], 2),
        ('meta 71/5/5, order 355, 2 short', _meta_b(71, 5, 5), [0, 92, 218, 269, 205, 88], 2),
        ('SL(2,5) x Z_3, order 360, 4 short', _sl2_cyc_b(5, 3), [0, 246, 216, 211, 99, 132], 2),
    ]
    return plan


def _safe(g, d, D):
    n, edges = g
    if lib.is_valid(n, edges, d, D):
        return g
    return (2, [(0, 1)])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return _safe(trivial(d, D), d, D)
    return run(d, D, seed, time_limit, make_plan(), FALLBACK)
