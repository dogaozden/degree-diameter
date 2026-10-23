"""Haar-graph and voltage-lift seed programs for the bipartite degree-diameter problem at diameter 5 (numpy only).

PHASE 1 (new construction, target d=10 D=5): a 2+2 voltage lift over a group G of order M in [1001, 1100].
  Base graph: A0, A1, B0, B1. Dart sets T_ij in G, |T00| = |T11| = a, |T01| = |T10| = 10 - a.
  Vertices (i, g) on the A side and (j, h) on the B side, with (A_i, g) ~ (B_j, t*g) for t in T_ij.
  This is 10-regular, bipartite, with 4M vertices. Right multiplication by G is an automorphism,
  so the diameter is at most 5 iff the balls of radius 5 around (A0,e), (A1,e), (B0,e), (B1,e) cover everything.
  Annealing over the dart sets minimises the total number of uncovered vertices.
  Any valid lift with M >= 1001 has more than 4000 vertices, which beats the record.

PHASE 2 (parent construction): Haar graphs of order 2|G| found by annealing over d-subsets of G.

Only graphs passing lib.is_valid are returned. Otherwise the smaller valid fallback is returned.
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
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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
    """Table of a group given as an (N, c) integer coordinate array (element 0 is the identity)."""
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


# ------------------------------------------------------------------------------- Phase 1: voltage lift 2+2

def lift_nb(MT, inv, T):
    """Neighbour table (4M, 10) of the 2+2 voltage lift.
    A_i,g has index i*M+g, B_j,h has index 2M+j*M+h. T[i][j] is an int64 array of darts."""
    M = MT.shape[0]
    G = np.arange(M, dtype=np.int64)
    rows = []
    for i in range(2):
        cols = [MT[T[i][j][:, None], G[None, :]].T.astype(np.int64) + (2 * M + j * M) for j in range(2)]
        rows.append(np.hstack(cols))
    for j in range(2):
        cols = [MT[inv[T[i][j]].astype(np.int64)[:, None], G[None, :]].T.astype(np.int64) + i * M for i in range(2)]
        rows.append(np.hstack(cols))
    return np.vstack(rows).astype(np.int64)


def lift_cost(nb, M):
    """Total uncovered vertices over the four orbit representatives (0 means diameter <= 5)."""
    n = 4 * M
    total = 0
    for s in (0, M, 2 * M, 3 * M):
        vis = np.zeros(n, dtype=bool)
        vis[s] = True
        fr = np.array([s], dtype=np.int64)
        for _ in range(5):
            nbrs = nb[fr].ravel()
            nbrs = nbrs[~vis[nbrs]]
            if nbrs.size == 0:
                break
            nbrs = np.unique(nbrs)
            vis[nbrs] = True
            fr = nbrs
        total += n - int(vis.sum())
    return total


def lift_search(MT, inv, a, deadline, rng, K=12, temp=2.0, patience=3000):
    """Annealing over the dart sets of the 2+2 lift. Returns (best darts, best cost)."""
    M = MT.shape[0]
    sizes = [[a, 10 - a], [10 - a, a]]

    def fresh():
        return [[rng.choice(M, sizes[i][j], replace=False).astype(np.int64) for j in range(2)] for i in range(2)]

    best, bestc = None, 10 ** 18
    T, cur, since = None, None, 0
    while time.monotonic() < deadline:
        if T is None:
            T = fresh()
            cur = lift_cost(lift_nb(MT, inv, T), M)
            since = 0
            if cur < bestc:
                best, bestc = [[b.copy() for b in row] for row in T], cur
            if cur == 0:
                return best, 0
        i, j = int(rng.integers(2)), int(rng.integers(2))
        blk = T[i][j]
        allv = np.concatenate([T[x][y] for x in range(2) for y in range(2)])
        k = int(rng.integers(len(blk)))
        old = blk[k]
        best_x, best_c = None, None
        for _ in range(K):
            if rng.random() < 0.5:
                x = int(rng.integers(M))
            else:
                t1, t2 = allv[rng.integers(len(allv), size=2)]
                x = int(MT[inv[t1], t2])
            if np.any(blk == x):
                continue
            blk[k] = x
            c = lift_cost(lift_nb(MT, inv, T), M)
            if best_c is None or c < best_c:
                best_x, best_c = x, c
        blk[k] = old
        if best_x is None:
            continue
        delta = best_c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            blk[k] = best_x
            cur = best_c
            if cur < bestc:
                best, bestc, since = [[b.copy() for b in row] for row in T], cur, 0
                if cur == 0:
                    return best, 0
            elif delta < 0:
                since = 0
        since += 1
        if since > patience:
            T = None
    return best, bestc


def lift_edges(nb, M):
    """Edge list of the lift (each edge taken once, from the A side)."""
    rows = nb[:2 * M].tolist()
    return 4 * M, [(u, v) for u, row in enumerate(rows) for v in row]


def metacyclic_candidates(lo, hi):
    """All (N, m, k, lam) with N = m*k in [lo, hi], k >= 2, m >= 3, lam a non-trivial unit mod m, lam^k = 1 mod m."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1:
                    continue
                out.append((N, "meta", (m, k, lam)))
    return out


def special_candidates(lo, hi):
    """Non-metacyclic groups in the order range: Heisenberg mod p and SL(2, p)."""
    out = []
    for p in (7, 11, 13):
        N = p ** 3
        if lo <= N <= hi:
            out.append((N, "heis", (p,)))
        N = p * (p * p - 1)
        if lo <= N <= hi:
            out.append((N, "sl2", (p,)))
    return out


def make_group(kind, args):
    if kind == "meta":
        return group_meta(*args)
    if kind == "heis":
        return group_heis(*args)
    if kind == "sl2":
        return group_sl2(*args)
    raise ValueError(kind)


def ordered_candidates(cands, rng):
    keyed = {}
    for c in cands:
        keyed.setdefault(c[0], []).append(c)
    order = []
    for N in sorted(keyed):
        grp = keyed[N]
        rng.shuffle(grp)
        order.extend(grp)
    return order


def voltage_phase(d, D, rng, deadline, SLICE=2.0):
    """New construction: 2+2 voltage lifts over metacyclic groups of order in [1001, 1100]."""
    order = ordered_candidates(metacyclic_candidates(1001, 1100), rng)
    if not order:
        return None
    idx = 0
    while time.monotonic() < deadline:
        _, kind, args = order[idx % len(order)]
        idx += 1
        now = time.monotonic()
        slice_end = min(deadline, now + SLICE)
        if slice_end - now < 0.2:
            break
        try:
            MT, inv = make_group(kind, args)
            a = int(rng.choice([4, 5, 6]))
            T, c = lift_search(MT, inv, a, slice_end, rng)
        except Exception:
            continue
        if T is not None and c == 0:
            try:
                M = MT.shape[0]
                nb = lift_nb(MT, inv, T)
                n, edges = lift_edges(nb, M)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                continue
    return None


# ------------------------------------------------------------------------------- Phase 2: Haar annealing

def _cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
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
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

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
        half = K // 2
        Xr = rng.integers(0, N, size=K - half)
        pa = S[rng.integers(0, d, size=half)]
        pb = S[rng.integers(0, d, size=half)]
        Xp = MT[inv[pa], pb] if half > 0 else np.zeros(0, dtype=np.int32)
        X = np.concatenate([Xr, Xp]).astype(np.int32)
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


def haar_edges(MT, S):
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ======================================================================================== cell: d10D5
TARGET = (10, 5)

LO, HI = 1792, 2200
SLICE_H = 4.0

FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def haar_phase(d, D, rng, deadline):
    """Parent construction: Haar graphs found by annealing over several groups."""
    order = ordered_candidates(metacyclic_candidates(LO, HI) + special_candidates(LO, HI), rng)
    idx = 0
    while order and time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.5:
            break
        _, kind, args = order[idx % len(order)]
        idx += 1
        slice_end = now + min(SLICE_H, remaining)
        try:
            MT, inv = make_group(kind, args)
            S, c = search(MT, inv, d, slice_end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g
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
    t0 = time.monotonic()
    rng = np.random.default_rng(seed)
    res = voltage_phase(d, D, rng, t0 + 0.65 * time_limit)
    if res is not None:
        return res
    return haar_phase(d, D, rng, t0 + 0.85 * time_limit)
