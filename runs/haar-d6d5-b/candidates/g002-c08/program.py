"""Haar-graph seed programs for the bipartite degree-diameter problem at diameter 5 (numpy only).

NEW FOR d6D5 (bold attempt): 2K-class voltage lifts over a non-abelian group, not Haar graphs.
Base graph: K A-classes and K B-classes. The number of darts between A_i and B_j is a small
matrix M with row and column sums 6, so every lifted vertex has degree 6. Each dart is a group
element s and joins (g, A_i) to (s*g, B_j). Right multiplication is an automorphism, so the
diameter is at most 5 iff, from one identity vertex of every class, the 5-ball covers the whole
graph. The cost is the number of uncovered (source, vertex) pairs, computed with vectorised
boolean propagation. Annealing moves one dart at a time. A success is verified with lib.is_valid.
With K=2 and |G| >= 172 the graph has >= 688 vertices (record 684). With K=3 and |G| >= 115 it has
>= 690 vertices.

If the lift search fails, the parent's Haar plan runs with the remaining budget. The parent's
precomputed valid Haar fallback (660 vertices) is still returned if that also fails.
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
    """Table of a group given as an (N, c) integer coordinate array (element 0 must be the identity)."""
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


# ------------------------------------------------------------------------------------ Haar search (parent)

def _cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by x, for every x in X."""
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
    """Score every single-slot replacement of S.  Returns (best cost, best S)."""
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
    """Local search over d-subsets of the group.  Returns (best S, best cost)."""
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


# --------------------------------------------------------------------------------- Haar graph helpers

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


def run(d, D, seed, time_limit, plan, fallback):
    """plan: list of (name, builder, S0 or None, seconds-weight); fallback: (builder, S) of a valid smaller graph."""
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


# ===================================================================== NEW: multi-class voltage lifts (d6D5)

TARGET = (6, 5)

# Dart-count matrices: rows index A-classes, columns index B-classes. All row and column sums are 6.
MAT2 = [((3, 3), (3, 3)), ((4, 2), (2, 4)), ((5, 1), (1, 5))]
MAT3 = [((2, 2, 2), (2, 2, 2), (2, 2, 2)), ((3, 2, 1), (2, 1, 3), (1, 3, 2))]


def _specs():
    """Candidate (K, dart matrix, group order N, group builder) tuples."""
    specs = []
    for N in range(115, 201):
        for k in range(2, 13):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1:
                    continue
                b = (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))
                if 172 <= N <= 200:
                    specs += [(2, mt, N, b) for mt in MAT2]
                if 115 <= N <= 150:
                    specs += [(3, mt, N, b) for mt in MAT3]
    specs += [(3, mt, 120, (lambda: group_sl2(5))) for mt in MAT3]
    specs += [(3, mt, 125, (lambda: group_heis(5))) for mt in MAT3]
    specs += [(3, mt, 136, (lambda: group_agl(17, 8))) for mt in MAT3]
    specs += [(3, mt, 156, (lambda: group_agl(13))) for mt in MAT3]
    return specs


def _lift_nb(MT, inv, blocks, K):
    """Neighbour matrix (2K*N, 6) of the lift. Class A_i is block i, class B_j is K+j."""
    N = MT.shape[0]
    NB = np.zeros((2 * K * N, 6), dtype=np.int64)
    ptrA = [0] * K
    ptrB = [0] * K
    for (i, j) in sorted(blocks):
        S = blocks[(i, j)]
        c = len(S)
        NB[i * N:(i + 1) * N, ptrA[i]:ptrA[i] + c] = (MT[S].astype(np.int64) + (K + j) * N).T
        NB[(K + j) * N:(K + j + 1) * N, ptrB[j]:ptrB[j] + c] = (MT[inv[S]].astype(np.int64) + i * N).T
        ptrA[i] += c
        ptrB[j] += c
    return NB


def _uncovered(NB, C, N):
    """Total number of (class source, vertex) pairs not within distance 5 of the source."""
    V = C * N
    reach = np.zeros((C, V), dtype=bool)
    reach[np.arange(C), np.arange(C) * N] = True
    for _ in range(5):
        reach = reach | reach[:, NB].any(axis=2)
    return C * V - int(reach.sum())


def _anneal(MT, inv, K, mat, deadline, rng, patience=20000, T=0.7):
    """Anneal the dart sets. Returns (K, N, NB) on cost 0, else None."""
    N = MT.shape[0]
    C = 2 * K
    keys = [(i, j) for i in range(K) for j in range(K) if mat[i][j] > 0]
    blocks = {key: rng.choice(N, mat[key[0]][key[1]], replace=False).astype(np.int64) for key in keys}
    cur = _uncovered(_lift_nb(MT, inv, blocks, K), C, N)
    best, since = cur, 0
    while cur > 0 and time.monotonic() < deadline:
        key = keys[int(rng.integers(len(keys)))]
        S = blocks[key]
        p = int(rng.integers(len(S)))
        x = int(rng.integers(N))
        if x in S:
            continue
        newS = S.copy()
        newS[p] = x
        blocks[key] = newS
        c2 = _uncovered(_lift_nb(MT, inv, blocks, K), C, N)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
            if cur < best:
                best, since = cur, 0
            else:
                since += 1
        else:
            blocks[key] = S
            since += 1
        if since > patience:
            return None
    if cur == 0:
        return K, N, _lift_nb(MT, inv, blocks, K)
    return None


def _lift_search(deadline, rng):
    specs = _specs()
    while time.monotonic() < deadline:
        K, mat, N, builder = specs[int(rng.integers(len(specs)))]
        try:
            MT, inv = builder()
        except Exception:
            continue
        slice_end = min(deadline, time.monotonic() + 4.0)
        res = _anneal(MT, inv, K, mat, slice_end, rng)
        if res is not None:
            return res
    return None


def _lift_edges(NB, K, N):
    """Edges of the lift; every edge has exactly one A endpoint, so each is listed once."""
    edges = []
    for u in range(K * N):
        for v in NB[u]:
            edges.append((u, int(v)))
    return 2 * K * N, edges


# ----------------------------------------------------------------------------------------------- fallback

PLAN = [
    ('meta 117/3/16, order 351, 2 short', lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21], 4),
    ('meta 71/5/5, order 355, 2 short', lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88], 4),
    ('SL(2,5) x Z_3, order 360, 4 short', lambda: group_times_cyclic(group_sl2(5), 3), [0, 246, 216, 211, 99, 132], 3),
]

FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    rng = np.random.default_rng(seed)
    try:
        res = _lift_search(t0 + 0.65 * time_limit, rng)
        if res is not None:
            K, N, NB = res
            n, edges = _lift_edges(NB, K, N)
            if lib.is_valid(n, edges, d, D):
                return n, edges
    except Exception:
        pass
    elapsed = time.monotonic() - t0
    tl2 = max(1.0, (0.92 * time_limit - elapsed) / 0.8)
    return run(d, D, seed, tl2, PLAN, FALLBACK)
