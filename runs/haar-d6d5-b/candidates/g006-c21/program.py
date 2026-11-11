"""Combined (d=6, D=5) search: Haar graphs over non-abelian groups (order just above 342) and
two-orbit group lifts over metacyclic groups (order 172..200, giving 4M > 684 vertices).
Every returned graph is checked with lib.is_valid; a verified 660-vertex Haar graph is the fallback.
"""
import itertools
import math
import time
from math import gcd

import numpy as np

import lib

TARGET = (6, 5)


# ============================================================ group tables (identity is index 0)

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int64)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) coordinate array (identity first) and vectorised product."""
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sorted_codes = codes[order]
    MT = np.empty((N, N), dtype=np.int64)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sorted_codes, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a,j)(b,l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = ((a[:, None] + pw[j][:, None] * a[None, :]) % m) * k + (j[:, None] + j[None, :]) % k
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p, order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k (maps t -> a t + b, a in the order-k subgroup of GF(q)*). Default k = q-1."""
    F = lib.GF(q)
    k = q - 1 if k is None else k
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    elems = [(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)]
    E = np.array(elems, dtype=np.int64)
    add, mt = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mt[X[..., 1], Y[..., 0]]], mt[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(E, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group with Z_k; element (g, c) -> g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    C = (np.arange(k)[:, None] + np.arange(k)[None, :]) % k
    MT4 = MT0[:, None, :, None] * k + C[None, :, None, :]
    return _finish(MT4.reshape(n0 * k, n0 * k))


# ============================================================ Haar graph search

def _cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def cost_haar(MT, inv, S):
    """Uncovered elements on both sides; 0 means the Haar graph of S has diameter <= 5."""
    N = MT.shape[0]
    Si = inv[S]
    total = 0
    for P in (MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()):
        total += N - int(_cover(MT, N, np.unique(P)).sum())
    return total


def search_haar(MT, inv, d, deadline, rng, K=8, T=0.45, patience=3000):
    """Annealing with random restarts over d-subsets; returns (S, cost), cost 0 when found."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    while time.monotonic() < deadline:
        S = np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int64)
        cur = cost_haar(MT, inv, S)
        since = 0
        while since < patience and time.monotonic() < deadline:
            if cur < bestc:
                best, bestc = S.copy(), cur
            if cur == 0:
                return S, 0
            i = int(rng.integers(d))
            others = np.delete(S, i)
            bestk, bestkc = None, None
            for _ in range(K):
                x = int(rng.integers(N))
                if x in others:
                    continue
                T2 = S.copy()
                T2[i] = x
                c2 = cost_haar(MT, inv, T2)
                if bestkc is None or c2 < bestkc:
                    bestkc, bestk = c2, T2
            if bestk is None:
                since += 1
                continue
            delta = bestkc - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = bestk, bestkc
                since = 0 if delta < 0 else since + 1
            else:
                since += 1
    return best, bestc


def haar_edges(MT, S):
    """A-vertex g is g, B-vertex g is N+g, edges (g,A)~(s*g,B)."""
    N = MT.shape[0]
    edges = []
    g = np.arange(N).tolist()
    for s in sorted({int(x) for x in S}):
        for a, b in zip(g, MT[s].tolist()):
            edges.append((a, N + b))
    return 2 * N, edges


# ============================================================ two-orbit group lifts (4M vertices)

PATTERNS = [
    [[3, 3], [3, 3]],
    [[2, 4], [4, 2]],
    [[4, 2], [2, 4]],
    [[1, 5], [5, 1]],
    [[5, 1], [1, 5]],
]


def build_nbr(MT, inv, M, volt):
    N = 4 * M
    nbr = np.empty((N, 6), dtype=np.int64)
    ar = np.arange(M, dtype=np.int64)
    ca = [0, 0]
    cb = [0, 0]
    for (i, j), vs in volt.items():
        for g in vs:
            nbr[i * M + ar, ca[i]] = (2 + j) * M + MT[ar, g]
            ca[i] += 1
            nbr[(2 + j) * M + ar, cb[j]] = i * M + MT[ar, inv[g]]
            cb[j] += 1
    return nbr


def cost2(nbr, N, M):
    total = 0
    for s in (0, M, 2 * M, 3 * M):
        vis = np.zeros(N, dtype=bool)
        vis[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(5):
            nb = nbr[front].ravel()
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            vis[nb] = True
            front = nb
        total += N - int(vis.sum())
    return total


def to_edges2(MT, M, volt):
    ar = np.arange(M, dtype=np.int64)
    E = []
    for (i, j), vs in volt.items():
        for g in vs:
            u = (i * M + ar).tolist()
            v = ((2 + j) * M + MT[ar, g]).tolist()
            E.extend(zip(u, v))
    return 4 * M, [(int(a), int(b)) for a, b in E]


def search2(MT, inv, M, deadline, rng, T=2.0, patience=4000):
    N = 4 * M
    while time.monotonic() < deadline:
        pat = PATTERNS[int(rng.integers(len(PATTERNS)))]
        volt = {}
        for i in range(2):
            for j in range(2):
                c = pat[i][j]
                volt[(i, j)] = [int(x) for x in rng.choice(M, c, replace=False)] if c > 0 else []
        cur = cost2(build_nbr(MT, inv, M, volt), N, M)
        pairs = [p for p in volt if volt[p]]
        since = 0
        while since < patience and time.monotonic() < deadline:
            if cur == 0:
                return volt
            p = pairs[int(rng.integers(len(pairs)))]
            k = int(rng.integers(len(volt[p])))
            x = int(rng.integers(M))
            if x in volt[p]:
                since += 1
                continue
            old = volt[p][k]
            volt[p][k] = x
            c2 = cost2(build_nbr(MT, inv, M, volt), N, M)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
                since = 0 if delta < 0 else since + 1
            else:
                volt[p][k] = old
                since += 1
        if cur == 0:
            return volt
    return None


def candidates2():
    """Metacyclic groups of order 172..200 (non-abelian), smallest first."""
    out = []
    for m in range(3, 201):
        for k in range(2, 200 // m + 1):
            n_ = m * k
            if n_ < 172 or n_ > 200:
                continue
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((n_, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
                    break
    out.sort(key=lambda t: t[0])
    return out[:8]


# ============================================================ fallback and trivial cases

FALLBACK_S = [0, 179, 116, 180, 47, 306]


def haar_fallback():
    MT, _ = group_meta(33, 10, 26)
    N = MT.shape[0]
    edges = []
    for s in FALLBACK_S:
        for g in range(N):
            edges.append((g, N + int(MT[s, g])))
    return 2 * N, edges


def trivial(d, D):
    try:
        if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
            n, e = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, e, d, D):
                return n, e
        n, e = lib.haar_graph(d, range(d))
        if lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return 2, [(0, 1)]


# ============================================================ entry point

HAAR_PLAN = [
    lambda: group_times_cyclic(group_heis(3), 13),   # order 351
    lambda: group_heis(7),                           # order 343
    lambda: group_times_cyclic(group_agl(9), 5),     # order 360
    lambda: group_times_cyclic(group_agl(5), 18),    # order 360
]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    best = None

    # Phase A: Haar graphs over non-abelian groups of order just above 342.
    phase_a_end = t0 + 0.5 * budget
    for idx, builder in enumerate(HAAR_PLAN):
        now = time.monotonic()
        rem = phase_a_end - now
        if rem <= 0.5:
            break
        end = now + rem / (len(HAAR_PLAN) - idx)
        try:
            MT, inv = builder()
            S, c = search_haar(MT, inv, d, end, rng)
            if S is not None and c == 0:
                n, edges = haar_edges(MT, S)
                if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                    best = (n, edges)
        except Exception:
            continue

    # Phase B: two-orbit lifts over metacyclic groups (4M vertices, need M >= 172 to beat 684).
    cands = candidates2()
    for idx, (n_, builder) in enumerate(cands):
        if best is not None and 4 * n_ <= best[0]:
            continue
        now = time.monotonic()
        rem = deadline - now
        if rem <= 0.5:
            break
        end = now + rem / (len(cands) - idx)
        try:
            MT, inv = builder()
            M = MT.shape[0]
            volt = search2(MT, inv, M, end, rng)
            if volt is None:
                continue
            n, edges = to_edges2(MT, M, volt)
            if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                best = (n, edges)
        except Exception:
            continue

    if best is not None:
        return best
    try:
        n, edges = haar_fallback()
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
