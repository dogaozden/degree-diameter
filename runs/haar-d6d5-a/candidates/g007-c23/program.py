"""Biregular voltage-lift search for the d=6, D=5 cell, with the Haar-graph search kept as a fallback.

NEW CONSTRUCTION.  Earlier versions used only Haar graphs: two base vertices joined by d parallel darts. Here the
base is a bipartite multigraph with k A-vertices and k B-vertices. Each base vertex has degree 6, and the multiplicity
matrix M (rows and columns summing to 6) gives the number of darts between each A-base and B-base vertex. A dart
(i, j, s) with voltage s in a group G of order N joins (i, g) to (k + j, g*s) for every g. Left multiplication by G
is an automorphism that acts regularly on each side, so the diameter is at most 5 iff every BFS ball of radius 5
around the 2k base vertices (at the identity) covers the whole graph. The cost is the total number of uncovered
vertices over those 2k sources, and cost 0 is valid.

Two lift families are tried, both over metacyclic non-abelian groups:
  * k = 3 with M = 2J, giving 6N vertices, for N = 115..118 (690..708 vertices).
  * k = 2 with M = [[3,3],[3,3]] or [[2,4],[4,2]], giving 4N vertices, for N = 172..174 (688..696 vertices).
Jobs are sorted by vertex count. Each one is annealed (voltage replacement moves, Metropolis acceptance, restarts)
within its time slice. A job is skipped once it cannot beat the best graph found so far.

SAFETY.  The earlier Haar-graph search (order 331..360 groups, plus the 660-vertex fallback) still runs for a
fraction of the budget. The largest checked valid graph among the lift result and the Haar result is returned.
Every returned graph is checked with lib.is_valid. If nothing valid is found, a trivially valid graph is returned.
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
    """GF(q) x| C_k: the maps t -> a*t + b with a in the subgroup of order k of GF(q)^* (default AGL(1, q))."""
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


def metacyclic_candidates(lo, hi, limit):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with lo <= m*k <= hi (one lam per (m, k)), smallest order first."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or lam % m == 1:
                    continue
                if pow(lam, k, m) == 1 % m:
                    out.append((m, k, lam))
                    break
        if len(out) >= limit:
            break
    return out[:limit]


# ================================================================ biregular voltage lifts (NEW)

LIFT_DEG = 6
D_TARGET = 5


def lift_adj(MT, inv, k, N, di, dj, ds):
    """Adjacency array (2kN, 6) of the lift. A-base i is vertex block i, B-base j is block k+j.
    A-vertex (i, g) ~ (k+j, g*s) for each dart (i, j, s); B-vertex (k+j, h) ~ (i, h*s^-1)."""
    ar = np.arange(N)
    adj = np.empty((2 * k * N, LIFT_DEG), dtype=np.int64)
    for i in range(k):
        idx = np.nonzero(di == i)[0]
        for c, t in enumerate(idx):
            adj[i * N:(i + 1) * N, c] = (k + int(dj[t])) * N + MT[ar, int(ds[t])]
    for j in range(k):
        idx = np.nonzero(dj == j)[0]
        for c, t in enumerate(idx):
            adj[(k + j) * N:(k + j + 1) * N, c] = int(di[t]) * N + MT[ar, int(inv[int(ds[t])])]
    return adj


def _ball(adj, src, R):
    """Number of vertices within distance R of src."""
    n = adj.shape[0]
    seen = np.zeros(n, dtype=bool)
    seen[src] = True
    front = np.array([src], dtype=np.int64)
    for _ in range(R):
        nb = adj[front].ravel()
        nb = np.unique(nb[~seen[nb]])
        if nb.size == 0:
            break
        seen[nb] = True
        front = nb
    return int(seen.sum())


def lift_cost(MT, inv, k, N, di, dj, ds):
    """Uncovered vertices summed over the 2k base sources (0 = diameter <= 5)."""
    adj = lift_adj(MT, inv, k, N, di, dj, ds)
    n = 2 * k * N
    return sum(n - _ball(adj, v * N, D_TARGET) for v in range(2 * k))


def random_darts(k, N, M, rng):
    """Random darts for multiplicity matrix M: M[i][j] distinct voltages for each pair (i, j)."""
    di, dj, ds = [], [], []
    for i in range(k):
        for j in range(k):
            vs = rng.choice(N, M[i][j], replace=False)
            for s in vs:
                di.append(i)
                dj.append(j)
                ds.append(int(s))
    return np.array(di, dtype=np.int64), np.array(dj, dtype=np.int64), np.array(ds, dtype=np.int64)


def lift_search(MT, inv, k, N, M, deadline, rng, temp=1.0, patience=2500):
    """Anneal the voltages of a lift until cost 0 or the deadline. Returns (best cost, di, dj, ds)."""
    T = LIFT_DEG * k
    di, dj, ds = random_darts(k, N, M, rng)
    cur = lift_cost(MT, inv, k, N, di, dj, ds)
    best = (cur, di.copy(), dj.copy(), ds.copy())
    since = 0
    while cur > 0 and time.monotonic() < deadline:
        t = int(rng.integers(T))
        s = int(rng.integers(N))
        same = (di == di[t]) & (dj == dj[t])
        same[t] = False
        if np.any(ds[same] == s):
            continue
        old = int(ds[t])
        ds[t] = s
        new = lift_cost(MT, inv, k, N, di, dj, ds)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = new
            if cur < best[0]:
                best = (cur, di.copy(), dj.copy(), ds.copy())
                since = 0
        else:
            ds[t] = old
        since += 1
        if since > patience:
            di, dj, ds = random_darts(k, N, M, rng)
            cur = lift_cost(MT, inv, k, N, di, dj, ds)
            since = 0
    return best


def lift_graph(MT, inv, k, N, di, dj, ds):
    """Edge list of the lift; every edge is listed once from its A-side endpoint."""
    adj = lift_adj(MT, inv, k, N, di, dj, ds)
    n = 2 * k * N
    edges = [(v, int(adj[v, c])) for v in range(k * N) for c in range(LIFT_DEG)]
    return n, edges


def lift_jobs():
    """(vertex count, k, M, m, k_group, lam) jobs, smallest vertex count first."""
    jobs = []
    for m, kk, lam in metacyclic_candidates(115, 118, 4):
        M3 = ((2, 2, 2), (2, 2, 2), (2, 2, 2))
        jobs.append((6 * m * kk, 3, M3, m, kk, lam))
    for m, kk, lam in metacyclic_candidates(172, 174, 3):
        for M2 in (((3, 3), (3, 3)), ((2, 4), (4, 2))):
            jobs.append((4 * m * kk, 2, M2, m, kk, lam))
    jobs.sort(key=lambda j: j[0])
    return jobs


def lift_run(deadline_total, rng):
    """Search the lift jobs in order of size; return the largest checked valid lift, or None."""
    jobs = lift_jobs()
    if not jobs:
        return None
    best, best_n = None, 0
    per = max(0.0, deadline_total - time.monotonic()) / len(jobs)
    for n_v, k, M, m, kk, lam in jobs:
        now = time.monotonic()
        if now >= deadline_total:
            break
        if n_v <= best_n:
            continue
        end = min(deadline_total, now + per)
        try:
            N = m * kk
            MT, inv = group_meta(m, kk, lam)
            c, di, dj, ds = lift_search(MT, inv, k, N, M, end, rng)
        except Exception:
            continue
        if c == 0:
            n, edges = lift_graph(MT, inv, k, N, di, dj, ds)
            if n > best_n and lib.is_valid(n, edges, 6, D_TARGET):
                best, best_n = (n, edges), n
    return best


# --------------------------------------------------------------------------------------------- Haar graph

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
            if len(X) == 0:
                continue
            cs = batch_costs(MT, inv, S, i, X)
            j = int(np.argmin(cs))
            if cs[j] < best:
                best, bestS = int(cs[j]), S.copy()
                bestS[i] = X[j]
    return best, bestS


def proposals(MT, inv, S, i, rng, K):
    """Candidate replacements for slot i: half are products a*b or a^-1*b of elements already in S, the rest uniform."""
    N = MT.shape[0]
    rest = np.delete(S, i)
    npr = K // 2
    a = rest[rng.integers(0, len(rest), npr)]
    b = S[rng.integers(0, len(S), npr)]
    prod = np.where(rng.integers(0, 2, npr) == 0, MT[inv[a], b], MT[a, b])
    xr = rng.integers(0, N, K - npr)
    X = np.concatenate([prod, xr]).astype(np.int32)
    return X[~np.isin(X, rest)]


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Local search over d-subsets of the group. Returns (best S, best cost)."""
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
        c1, S1 = one_swap_scan(MT, inv, S0, time.monotonic() + 0.25 * max(0.0, deadline - time.monotonic()))
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
        X = proposals(MT, inv, S, i, rng, K)
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
    """plan: list of (name, order, builder, S0 or None, weight), sorted by order ascending.
    Keeps the largest checked valid graph found; a candidate is skipped if it cannot beat the current best."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.85 * time_limit
    rng = np.random.default_rng(seed)
    total_w = sum(e[4] for e in plan)
    best_g, best_n = None, 0
    for name, order, builder, S0, w in plan:
        now = time.monotonic()
        if now >= deadline_all:
            break
        if 2 * order <= best_n:
            total_w -= w
            continue
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, S0, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None and g[0] > best_n:
                best_g, best_n = g, g[0]
    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None and (best_g is None or g[0] > best_n):
            best_g = g
    except Exception:
        pass
    if best_g is not None:
        return best_g
    return trivial(d, D)


# ======================================================================================== cell: d6D5
TARGET = (6, 5)

# Near-miss seeds (element indices of the group table), from earlier searches.
NEAR = {(117, 3), (71, 5)}


def _plan():
    E = []
    # Safety tier: orders 331..341 improve on the 660-vertex fallback.
    for m, k, lam in metacyclic_candidates(331, 341, 6):
        E.append((f'meta {m}/{k}/{lam}', m * k,
                  (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 0.5))
    # Order 342 ties the record (684 vertices): affine group AGL(1,19) and a metacyclic group.
    E.append(('AGL(1,19), order 342', 342, lambda: group_agl(19), None, 1.5))
    for m, k, lam in metacyclic_candidates(342, 342, 2):
        E.append((f'meta {m}/{k}/{lam}, order 342', m * k,
                  (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 1.0))
    # Beat-the-record tier: order > 342.
    E.append(('Heisenberg mod 7, order 343', 343, lambda: group_heis(7), None, 2.0))
    for m, k, lam in metacyclic_candidates(343, 360, 8):
        if (m, k) in NEAR:
            continue
        E.append((f'meta {m}/{k}/{lam}, order {m * k}', m * k,
                  (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 1.0))
    # Near misses with seeds (2 short at 351 and 355, 4 short at 360).
    E.append(('meta 117/3/16, order 351, 2 short', 351,
              lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21], 4.0))
    E.append(('meta 71/5/5, order 355, 2 short', 355,
              lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88], 4.0))
    E.append(('SL(2,5) x Z_3, order 360, 4 short', 360,
              lambda: group_times_cyclic(group_sl2(5), 3), [0, 246, 216, 211, 99, 132], 3.0))
    E.sort(key=lambda e: e[1])
    return E


PLAN = _plan()

# Valid smaller Haar graph (order 330, 660 vertices), used only if nothing better is found.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    rng = np.random.default_rng(seed)
    cands = []
    try:
        lift_best = lift_run(t0 + 0.6 * time_limit, rng)
        if lift_best is not None:
            cands.append(lift_best)
    except Exception:
        pass
    try:
        haar_best = run(d, D, seed, 0.25 * time_limit, PLAN, FALLBACK)
        cands.append(haar_best)
    except Exception:
        pass
    best = None
    for n, edges in sorted(cands, key=lambda g: -g[0]):
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
            break
    if best is not None:
        return best
    return trivial(d, D)
