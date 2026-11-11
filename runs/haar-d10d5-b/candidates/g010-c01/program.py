"""Bold change for the d10D5 target: 2-orbit and 3-orbit voltage lifts of group tables, found by annealing.

CONSTRUCTION.  Let G be a group of order N with multiplication table MT (MT[a, b] = a*b).  Use k A-orbits and
k B-orbits.  Each of the d layers t carries a permutation P[t] of range(k) and a voltage C[t, u] in G.  The
A-vertex (u, x) is joined to the B-vertex (P[t][u], x * C[t, u]) for every layer t.  Left multiplication
x -> h*x on both sides is an automorphism, so the diameter is at most D iff each of the 2k orbit
representatives (block start, group element 0) reaches every vertex within D steps.  COST counts the
unreached vertices over those 2k breadth-first searches, plus a large penalty for repeated neighbours.
Cost 0 means the lift is exactly valid, and the result is re-checked with lib.is_valid before it is returned.

FALLBACKS.  If no lift reaches cost 0 in its time share, a validated smaller Haar graph is returned, and
trivial(d, D) is the last resort.  The calibration case d3D3 uses the same trivial() path as before.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (10, 5)
PATIENCE = 4000
BIG_SCALE = 4


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
    """Heisenberg group mod p, order p^3, identity (0,0,0) first."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, identity first, order p(p^2-1)."""
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
    """GF(q) x| C_k (default k = q-1, i.e. AGL(1, q)), identity first."""
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


def _meta_builder(m, k):
    """Builder for Z_m x| Z_k with a nontrivial lam of order dividing k."""
    lam = next(x for x in range(2, m) if pow(x, k, m) == 1)
    return lambda: group_meta(m, k, lam)


# ------------------------------------------------------------------------------------ voltage lifts

def _update_layer(nbr, MT, inv, P, C, t, k, N):
    """Recompute the columns of layer t in the neighbour table nbr (2kN x d)."""
    Pt = P[t]
    Pinv = np.argsort(Pt)
    base = k * N
    for u in range(k):
        nbr[u * N:(u + 1) * N, t] = base + int(Pt[u]) * N + MT[:, int(C[t, u])]
    for v in range(k):
        u = int(Pinv[v])
        nbr[base + v * N: base + (v + 1) * N, t] = u * N + MT[:, int(inv[int(C[t, u])])]


def _energy(nbr, P, C, k, N, d, D, BIG):
    """Unreached vertices summed over the 2k orbit representatives, plus a penalty for repeated neighbours."""
    n = nbr.shape[0]
    codes = P * N + C
    dups = 0
    for u in range(k):
        dups += d - len(np.unique(codes[:, u]))
    bad = 0
    for j in range(2 * k):
        s = j * N
        vis = np.zeros(n, dtype=bool)
        vis[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(D):
            mark = np.zeros(n, dtype=bool)
            mark[nbr[front].ravel()] = True
            new = mark & ~vis
            if not new.any():
                break
            vis |= new
            front = np.flatnonzero(new)
        bad += n - int(np.count_nonzero(vis))
    return bad + BIG * dups


def _anneal(MT, inv, k, d, D, deadline, rng):
    """Simulated annealing over layer permutations and voltages.  Returns (P, C) with cost 0, or None."""
    N = MT.shape[0]
    n = 2 * k * N
    BIG = BIG_SCALE * n

    def fresh():
        P = np.array([rng.permutation(k) for _ in range(d)], dtype=np.int64)
        C = rng.integers(0, N, size=(d, k)).astype(np.int64)
        nbr = np.empty((n, d), dtype=np.int64)
        for t in range(d):
            _update_layer(nbr, MT, inv, P, C, t, k, N)
        return P, C, nbr

    P, C, nbr = fresh()
    cur = _energy(nbr, P, C, k, N, d, D, BIG)
    best, bestP, bestC = cur, P.copy(), C.copy()
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    since = 0
    T0, T1 = 6.0, 0.4
    while best > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - start) / span)
        t = int(rng.integers(d))
        saved = nbr[:, t].copy()
        if rng.random() < 0.75:
            kind = 0
            u = int(rng.integers(k))
            oldc = int(C[t, u])
            C[t, u] = int(rng.integers(N))
        else:
            kind = 1
            u1, u2 = (int(x) for x in rng.choice(k, 2, replace=False))
            P[t, u1], P[t, u2] = P[t, u2], P[t, u1]
        _update_layer(nbr, MT, inv, P, C, t, k, N)
        new = _energy(nbr, P, C, k, N, d, D, BIG)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
            if cur < best:
                best, bestP, bestC, since = cur, P.copy(), C.copy(), 0
                if best == 0:
                    break
            else:
                since += 1
        else:
            nbr[:, t] = saved
            if kind == 0:
                C[t, u] = oldc
            else:
                P[t, u1], P[t, u2] = P[t, u2], P[t, u1]
            since += 1
        if since > PATIENCE:
            P, C = bestP.copy(), bestC.copy()
            for _ in range(3):
                C[int(rng.integers(d)), int(rng.integers(k))] = int(rng.integers(N))
            for tt in range(d):
                _update_layer(nbr, MT, inv, P, C, tt, k, N)
            cur = _energy(nbr, P, C, k, N, d, D, BIG)
            since = 0
    if best == 0:
        return bestP, bestC
    return None


def _graph(MT, inv, k, d, P, C):
    """Edge list of the lift for (P, C): A-vertices 0..kN-1, B-vertices kN..2kN-1."""
    N = MT.shape[0]
    n = 2 * k * N
    nbr = np.empty((n, d), dtype=np.int64)
    for t in range(d):
        _update_layer(nbr, MT, inv, P, C, t, k, N)
    A = np.repeat(np.arange(k * N, dtype=np.int64), d)
    B = nbr[:k * N].ravel()
    edges = list(zip(A.tolist(), B.tolist()))
    return n, edges


# --------------------------------------------------------------------------- Haar fallback and trivial

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------------------------------- plan

# (name, group builder, orbits per side k, time weight).  Each group has order near 1000 (k=2) or 672 (k=3).
PLAN = [
    ('AGL(1,32) lift k=2, order 992', lambda: group_agl(32), 2, 12),
    ('SL(2,7) x Z_3 lift k=2, order 1008', lambda: group_times_cyclic(group_sl2(7), 3), 2, 12),
    ('meta 101/10 lift k=2, order 1010', _meta_builder(101, 10), 2, 8),
    ('Heis(7) x Z_3 lift k=2, order 1029', lambda: group_times_cyclic(group_heis(7), 3), 2, 8),
    ('SL(2,7) x Z_2 lift k=3, order 672', lambda: group_times_cyclic(group_sl2(7), 2), 3, 5),
]

# Validated smaller Haar graph (order 1791, 3582 vertices), used only if no lift reaches cost 0.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline_all = t0 + 0.72 * time_limit
    rng = np.random.default_rng(seed)
    total_w = sum(item[3] for item in PLAN)
    for name, builder, k, w in PLAN:
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            res = _anneal(MT, inv, k, d, D, end, rng)
            if res is not None:
                P, C = res
                n, edges = _graph(MT, inv, k, d, P, C)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
        except Exception:
            continue
    try:
        MT, inv = FALLBACK[0]()
        n, edges = haar_edges(MT, FALLBACK[1])
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
