"""Haar-graph race for the bipartite degree-diameter problem, diameter 5 (numpy only).

A Haar graph over a group G with connection set S (|S| = d) has 2|G| vertices and is d-regular.
It has diameter <= 5 iff cost(S) = 0, where cost counts group elements left uncovered by the
words (S^-1 S)^2 and (S S^-1)^2.  This version runs a successive-halving race over many groups of
order just above 2000 (non-abelian products, AGL, Heisenberg, SL(2,p), and random metacyclic
groups), annealing each one and keeping the better half every round.  Any cost-0 set is built and
checked with lib.is_valid before it is returned.  Otherwise a valid smaller Haar graph is returned.
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


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) coordinate array (element 0 = identity) and a vectorised product."""
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
    e = np.array(list(__import__("itertools").product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, order p(p^2-1)."""
    import itertools
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
    """GF(q) x| C_k: maps t -> a*t + b with a in the order-k subgroup of GF(q)^* (default AGL(1, q))."""
    F = lib.GF(q)
    k = q - 1 if k is None else k
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
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


def is_prime(n):
    return n > 1 and all(n % q for q in range(2, int(n ** 0.5) + 1))


# ------------------------------------------------------------------------------------------------ cost

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
    """cost of S with slot i replaced by x, for every x in X (only slot-i words are recomputed)."""
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


# ---------------------------------------------------------------------------------------- annealing

def random_set(N, d, rng):
    return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)


def anneal(MT, inv, d, st, end, rng, K=24, temp=0.45, patience=4000):
    """Anneal the state dict st = {S, cur, best, bestc} until time end or a cost-0 set is found."""
    N = MT.shape[0]
    S, cur, since = st["S"], st["cur"], 0
    while time.monotonic() < end and st["bestc"] > 0:
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
            if cur < st["bestc"]:
                st["bestc"], st["best"], since = cur, S.copy(), 0
            elif delta < 0:
                since = 0
        since += 1
        if since > patience:
            S = random_set(N, d, rng)
            cur = cost(MT, inv, S)
            since = 0
            if cur < st["bestc"]:
                st["bestc"], st["best"] = cur, S.copy()
    st["S"], st["cur"] = S, cur


# ---------------------------------------------------------------------------------- graph and check

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------ candidate groups

FIXED = [
    ('SL(2,7) x Z6', lambda: group_times_cyclic(group_sl2(7), 6)),            # 2016
    ('Heis(7) x Z6', lambda: group_times_cyclic(group_heis(7), 6)),           # 2058
    ('AGL(1,13) x Z13', lambda: group_times_cyclic(group_agl(13), 13)),       # 2028
    ('AGL(1,16) x Z9', lambda: group_times_cyclic(group_agl(16), 9)),         # 2160
    ('SL(2,5) x Z17', lambda: group_times_cyclic(group_sl2(5), 17)),          # 2040
    ('Heis(5) x Z17', lambda: group_times_cyclic(group_heis(5), 17)),         # 2125
    ('AGL(1,17) x Z8', lambda: group_times_cyclic(group_agl(17), 8)),         # 2176
]


def metacyclic_options(lo=2001, hi=2200):
    """(p, k, lams) for Z_p x|_lam Z_k with p prime, p*k in [lo, hi], and lam != 1 with lam^k = 1 mod p."""
    opts = []
    for p in range(7, 400):
        if not is_prime(p):
            continue
        for k in range(2, hi // p + 1):
            if not (lo <= p * k <= hi):
                continue
            lams = [l for l in range(2, p) if pow(l, k, p) == 1]
            if lams:
                opts.append((p, k, lams))
    return opts


def make_groups(rng):
    """A shuffled subset of the fixed groups plus two random metacyclic groups."""
    fixed = [FIXED[i] for i in rng.permutation(len(FIXED))[:5]]
    out = list(fixed)
    opts = metacyclic_options()
    if opts:
        for idx in rng.choice(len(opts), min(2, len(opts)), replace=False):
            p, k, lams = opts[int(idx)]
            lam = lams[int(rng.integers(len(lams)))]
            out.append((f"Z{p}:Z{k} lam={lam}", (lambda p=p, k=k, lam=lam: group_meta(p, k, lam))))
    return out


# ------------------------------------------------------------------------------------------- race

def race(d, D, rng, end):
    alive = []
    for name, builder in make_groups(rng):
        if time.monotonic() > end - 1.0:
            break
        try:
            MT, inv = builder()
        except Exception:
            continue
        N = MT.shape[0]
        if N <= 2000:          # a group of order <= 2000 gives at most the record
            continue
        S = random_set(N, d, rng)
        c = cost(MT, inv, S)
        st = {"S": S, "cur": c, "best": S.copy(), "bestc": c}
        if c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g
            continue
        alive.append({"name": name, "MT": MT, "inv": inv, "st": st})

    slice_s = 1.0
    while alive and time.monotonic() < end:
        survivors = []
        for g in alive:
            now = time.monotonic()
            if now >= end:
                survivors.append(g)
                continue
            anneal(g["MT"], g["inv"], d, g["st"], min(end, now + slice_s), rng)
            if g["st"]["bestc"] == 0:
                gr = checked(g["MT"], g["st"]["best"], d, D)
                if gr is not None:
                    return gr
                continue   # a false cost-0 is dropped
            survivors.append(g)
        survivors.sort(key=lambda g: g["st"]["bestc"])
        keep = max(1, (len(survivors) + 1) // 2)
        alive = survivors[:keep]
        slice_s *= 2
    return None


# ================================================================================== target cell

TARGET = (10, 5)

# Valid smaller Haar graph (3582 vertices), used whenever the race finds nothing.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    end = t0 + max(5.0, min(0.80 * time_limit, time_limit - 10.0))
    rng = np.random.default_rng(seed)
    try:
        g = race(d, D, rng, end)
        if g is not None:
            return g
    except Exception:
        pass
    try:
        MT, inv = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
