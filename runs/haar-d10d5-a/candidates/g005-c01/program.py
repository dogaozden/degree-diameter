"""Portfolio Haar-graph search for the diameter-5 bipartite degree-diameter problem (numpy only).

A Haar graph over a group G with connection set S (|S| = d) has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G. This version has two changes from the parent:

1. Targeted proposals (new): pick an uncovered element u of one side. Setting slot i to
   x = s_j * u^-1 (side 0) or x = u * s_j (side 1) makes u a pair product immediately, so
   the move covers a known gap instead of a random one. Half of each batch is targeted.
2. Ascending-skip portfolio: groups are drawn in random order from a pool of metacyclic,
   SL(2,7)xZ6, Heis(7)xZ6 and AGL-type groups with order in [LO, HI]. A group whose graph
   would not beat the current best valid graph is skipped.

Every returned graph is checked with lib.is_valid. The fallback is a valid Haar graph of
order 3582, and K_{d,d} or a smaller graph for the last resort.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
LO, HI = 1792, 2170                       # group orders; 2|G| > 4000 needs |G| > 2000
FB_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]   # valid for group_meta(199, 9, 180)


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l)."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) coordinate array (element 0 = identity)."""
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
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p,
                         (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q, k):
    """GF(q) x| C_k where C_k is the order-k subgroup of GF(q)^*. q prime."""
    F = lib.GF(q)
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    assert len(H) == k
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------ cost machinery

def uncovered(MT, inv, S):
    """Two arrays: the elements not in (S^-1 S)^2 (side 0) and not in (S S^-1)^2 (side 1)."""
    N = MT.shape[0]
    Si = inv[S]
    out = []
    for P in (np.unique(MT[Si[:, None], S[None, :]]), np.unique(MT[S[:, None], Si[None, :]])):
        cov = np.zeros(N, dtype=bool)
        cov[MT[P[:, None], P[None, :]].ravel()] = True
        out.append(np.nonzero(~cov)[0])
    return out


def cost(MT, inv, S):
    """Number of uncovered elements on both sides (0 means a valid diameter-5 Haar graph)."""
    return sum(int(u.size) for u in uncovered(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Exact cost of S with slot i replaced by each x in X (incremental word counting)."""
    N = MT.shape[0]
    K = len(X)
    rest = np.delete(S, i)
    total = np.zeros(K, dtype=np.int64)
    offs = (np.arange(K, dtype=np.int64) * N)[:, None]
    ri = inv[rest]
    xi = inv[X]
    for side in (0, 1):
        if side == 0:
            F = np.unique(MT[ri[:, None], rest[None, :]])
            Q = np.concatenate([MT[xi[:, None], rest[None, :]], MT[ri[None, :], X[:, None]]], axis=1)
        else:
            F = np.unique(MT[rest[:, None], ri[None, :]])
            Q = np.concatenate([MT[X[:, None], ri[None, :]], MT[rest[None, :], xi[:, None]]], axis=1)
        base = np.zeros(N, dtype=bool)
        base[MT[F[:, None], F[None, :]].ravel()] = True
        W = np.concatenate([MT[Q[:, :, None], F[None, None, :]].reshape(K, -1),
                            MT[F[None, None, :], Q[:, :, None]].reshape(K, -1),
                            MT[Q[:, :, None], Q[:, None, :]].reshape(K, -1)], axis=1)
        new = ~base[W]
        flat = (W + offs)[new]
        cnt = np.bincount(flat, minlength=K * N).reshape(K, N)
        total += N - int(base.sum()) - (cnt > 0).sum(axis=1)
    return total


# ----------------------------------------------------- targeted proposals (new idea)

def propose(MT, inv, S, i, unc, rng, K):
    """Candidates for slot i. Even entries cover a random uncovered element u directly:
    side 0: x = s_j * u^-1 gives inv(x) s_j = u; side 1: x = u * s_j gives x inv(s_j) = u.
    Odd entries are uniform random group elements."""
    N = MT.shape[0]
    d = S.size
    avail = [s for s in (0, 1) if unc[s].size]
    X = np.empty(K, dtype=np.int64)
    for t in range(K):
        if avail and t % 2 == 0:
            side = avail[int(rng.integers(len(avail)))]
            u = int(unc[side][int(rng.integers(unc[side].size))])
            j = int(rng.integers(d - 1))
            j = j if j < i else j + 1
            sj = int(S[j])
            if side == 0:
                X[t] = MT[sj, inv[u]]
            else:
                X[t] = MT[u, sj]
        else:
            X[t] = int(rng.integers(N))
    return X


def anneal(MT, inv, d, deadline, rng, K=24, temp=0.4, patience=2500):
    """Annealing with targeted proposals and restarts. Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 1 << 30
    while time.monotonic() < deadline:
        S = rng.choice(N, d, replace=False).astype(np.int32)
        cur = cost(MT, inv, S)
        unc = uncovered(MT, inv, S)
        if cur < bestc:
            best, bestc = S.copy(), cur
            if cur == 0:
                return best, 0
        bestrun, since = cur, 0
        while since < patience and time.monotonic() < deadline:
            i = int(rng.integers(d))
            X = propose(MT, inv, S, i, unc, rng, K).astype(np.int32)
            X = X[~np.isin(X, np.delete(S, i))]
            if X.size == 0:
                since += 1
                continue
            cs = batch_costs(MT, inv, S, i, X)
            j = int(np.argmin(cs + rng.random(cs.size) * 0.5))
            delta = int(cs[j]) - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                S[i] = X[j]
                cur = int(cs[j])
                unc = uncovered(MT, inv, S)
                if cur < bestc:
                    best, bestc = S.copy(), cur
                    if cur == 0:
                        return best, 0
                if cur < bestrun:
                    bestrun, since = cur, 0
                else:
                    since += 1
            else:
                since += 1
    return best, bestc


# ------------------------------------------------------------------------- graphs

def haar_edges(MT, S):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B) for s in S."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None unless lib.is_valid accepts it."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def candidate_specs(lo, hi):
    """List of (order, builder) for groups with lo <= order <= hi."""
    specs = []
    for k in range(2, 11):
        for m in range(max(2, -(-lo // k)), hi // k + 1):
            n = m * k
            if n < lo or n > hi:
                continue
            lams = []
            for lam in range(m - 1, 1, -1):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    lams.append(lam)
                    if len(lams) >= 2:
                        break
            for lam in lams:
                specs.append((n, lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
    extra = [
        (2016, lambda: group_times_cyclic(group_sl2(7), 6)),
        (2058, lambda: group_times_cyclic(group_heis(7), 6)),
        (47 * 23 * 2, lambda: group_times_cyclic(group_agl(47, 23), 2)),
        (37 * 18 * 3, lambda: group_times_cyclic(group_agl(37, 18), 3)),
        (43 * 21 * 2, lambda: group_times_cyclic(group_agl(43, 21), 2)),
        (31 * 15 * 4, lambda: group_times_cyclic(group_agl(31, 15), 4)),
    ]
    for order, make in extra:
        if lo <= order <= hi:
            specs.append((order, make))
    return specs


# ---------------------------------------------------------------------- entry points

def generic(d, D):
    """Valid small graph for any other case, always checked with lib.is_valid."""
    cands = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 16:
        cands.append(lambda: lib.projective_plane_incidence(d - 1))
    if D >= 2 and d >= 1:
        cands.append(lambda: lib.haar_graph(d, range(d)))     # K_{d,d}
    if D >= 1 and d >= 1:
        cands.append(lambda: (2, [(0, 1)]))
    for make in cands:
        try:
            n, e = make()
            if lib.is_valid(n, e, d, D):
                return n, e
        except Exception:
            pass
    return 1, []


def run_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.85 * time_limit - 1.0
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = group_meta(199, 9, 180)
        best = checked(MT, np.array(FB_S, dtype=np.int32), d, D)
    except Exception:
        best = None

    pool = candidate_specs(LO, HI)
    idx = rng.permutation(len(pool))
    slice_len = max(2.0, 0.09 * time_limit)

    for pi in idx:
        order, make = pool[int(pi)]
        now = time.monotonic()
        if now >= end:
            break
        if best is not None and 2 * order <= best[0]:
            continue
        dl = min(end, now + slice_len)
        try:
            MT, inv = make()
            S, c = anneal(MT, inv, d, dl, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None and (best is None or g[0] > best[0]):
                best = g

    if best is None:
        return generic(d, D)
    return best


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return generic(d, D)
    return run_target(d, D, seed, time_limit)
