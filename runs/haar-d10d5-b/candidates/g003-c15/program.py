"""Combined bipartite degree-diameter search for d=10, D=5.

Two families run round-robin under one deadline:
  * Haar graphs over non-abelian groups (SL(2,7) x Z6, Heis(7) x Z6, AGL(1,13) x Z13,
    AGL(1,16) x Z9, and random metacyclic groups just above the threshold 1791).
    Annealing on the connection set S with incremental cost (uncovered group elements).
  * Multi-orbit voltage lifts over metacyclic groups with p base vertices per side,
    annealing on the voltages with cost = unreached (source, vertex) pairs.

Any zero-cost configuration is checked with lib.is_valid before it replaces the incumbent.
The incumbent starts as the valid Haar graph over Z_199 x| Z_9 (3582 vertices), so the
output is never worse than that.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10
POOL = 6

FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------- group tables

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
    """Table of a group given as an (N, c) coordinate array (element 0 = identity) and vectorised product."""
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
    """GF(q) x| C_k (default k = q-1, AGL(1, q)); q a prime power."""
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


def random_metacyclic(N, rng):
    """A random metacyclic group Z_m x| Z_k of order N (cyclic if no non-trivial choice)."""
    cands = [(m, N // m) for m in range(2, N) if N % m == 0 and N // m >= 2]
    if not cands:
        return group_meta(1, N, 1)
    m, k = cands[int(rng.integers(len(cands)))]
    rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    r = rs[int(rng.integers(len(rs)))] if rs else 1
    return group_meta(m, k, r)


# ----------------------------------------------------------------------------- Haar search

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
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
    """Cost of S with slot i replaced by each x in X (only slot-i words are recomputed)."""
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


def haar_gen(MT, inv, d, rng, K=24, temp=0.45, patience=4000):
    """Generator: one annealing step per yield.  Yields ('found', S) at cost 0, then ends."""
    N = MT.shape[0]
    S, cur, since = None, None, 0
    while True:
        if S is None:
            S = np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)
            cur = cost(MT, inv, S)
            since = 0
            if cur == 0:
                yield ('found', S.copy())
                return
        i = int(rng.integers(d))
        X = rng.integers(0, N, size=K).astype(np.int32)
        X = X[~np.isin(X, np.delete(S, i))]
        if len(X) == 0:
            yield None
            continue
        cs = batch_costs(MT, inv, S, i, X)
        j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
        delta = int(cs[j]) - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S[i] = X[j]
            cur = int(cs[j])
            if cur == 0:
                yield ('found', S.copy())
                return
            if delta < 0:
                since = 0
        since += 1
        if since > patience:
            S = None
        yield None


def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N, dtype=np.int64)
    edges = []
    for s in S:
        edges.extend(zip(g.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


FIXED_GROUPS = [
    (2016, lambda: group_times_cyclic(group_sl2(7), 6)),
    (2058, lambda: group_times_cyclic(group_heis(7), 6)),
    (2028, lambda: group_times_cyclic(group_agl(13), 13)),
    (2160, lambda: group_times_cyclic(group_agl(16), 9)),
]


def spawn_haar(best_n, rng, d):
    lo = best_n // 2 + 1
    ok = [f for f in FIXED_GROUPS if f[0] >= lo]
    if ok and rng.random() < 0.4:
        order, make = ok[int(rng.integers(len(ok)))]
        N = order
        MT, inv = make()
    else:
        N = lo + int(rng.integers(0, 301))
        MT, inv = random_metacyclic(N, rng)
    gen = haar_gen(MT, inv, d, rng)
    return {'gen': gen, 'n': 2 * N, 'conv': lambda S, MT=MT: haar_edges(MT, S)}


# ----------------------------------------------------------------------------- multi-orbit lifts

def compositions(total, parts):
    """All ordered sums of `parts` positive integers equal to total."""
    if parts == 1:
        return [(total,)]
    out = []
    for a in range(1, total - parts + 2):
        for rest in compositions(total - a, parts - 1):
            out.append((a,) + rest)
    return out


COMPS = {p: compositions(TARGET_D, p) for p in range(1, 5)}


def layout(p, w):
    """Dart layout for the circulant base pattern."""
    di, dj = [], []
    for i in range(p):
        for j in range(p):
            for _ in range(w[(j - i) % p]):
                di.append(i)
                dj.append(j)
    T = len(di)
    colA = [0] * T
    colB = [0] * T
    cnt = [0] * p
    for t in range(T):
        colA[t] = cnt[di[t]]
        cnt[di[t]] += 1
    cnt = [0] * p
    for t in range(T):
        colB[t] = cnt[dj[t]]
        cnt[dj[t]] += 1
    di_a = np.array(di, dtype=np.int64)
    dj_a = np.array(dj, dtype=np.int64)
    blocks_of = []
    for t in range(T):
        blocks_of.append(np.nonzero((di_a == di[t]) & (dj_a == dj[t]))[0])
    return di_a, dj_a, colA, colB, blocks_of


def cost_of(adj, p, N, D):
    """Number of (source, vertex) pairs at distance > D; sources are the 2p base-vertex identities."""
    n = adj.shape[0]
    S = 2 * p
    src = [i * N for i in range(p)] + [(p + j) * N for j in range(p)]
    reach = np.zeros((S, n), dtype=bool)
    reach[np.arange(S), src] = True
    for _ in range(D):
        reach = reach | reach[:, adj].any(axis=2)
    return S * n - int(np.count_nonzero(reach))


def edges_from_adj(adj):
    n, d = adj.shape
    src = np.repeat(np.arange(n, dtype=np.int64), d)
    dst = adj.ravel()
    mask = src < dst
    return list(zip(src[mask].tolist(), dst[mask].tolist()))


def anneal_gen(p, w, N, MT, inv, d, D, rng):
    """Generator: one annealing step per yield.  Yields ('found', adj) at cost 0, then ends."""
    di, dj, colA, colB, blocks_of = layout(p, w)
    T = len(di)
    n = 2 * p * N

    def set_dart(adj, t, g):
        i = int(di[t])
        j = int(dj[t])
        adj[i * N:(i + 1) * N, colA[t]] = p * N + j * N + MT[g]
        adj[(p + j) * N:(p + j + 1) * N, colB[t]] = i * N + MT[inv[g]]

    while True:
        dg = np.zeros(T, dtype=np.int64)
        for i in range(p):
            for j in range(p):
                ts = np.nonzero((di == i) & (dj == j))[0]
                if len(ts):
                    dg[ts] = rng.choice(N, len(ts), replace=False)
        adj = np.empty((n, d), dtype=np.int64)
        for t in range(T):
            set_dart(adj, t, int(dg[t]))
        cur = cost_of(adj, p, N, D)
        if cur == 0:
            yield ('found', adj.copy())
            return
        L = 3000
        for step in range(L):
            t = int(rng.integers(T))
            taken = dg[blocks_of[t]]
            g_new = int(rng.integers(N))
            if np.any(taken == g_new):
                yield None
                continue
            g_old = int(dg[t])
            set_dart(adj, t, g_new)
            dg[t] = g_new
            c = cost_of(adj, p, N, D)
            temp = 0.3 + 1.7 * (1.0 - step / L)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
                if cur == 0:
                    yield ('found', adj.copy())
                    return
            else:
                set_dart(adj, t, g_old)
                dg[t] = g_old
            yield None


def spawn_lift(best_n, rng, d, D):
    p = int(rng.integers(1, 5))
    lo = best_n // (2 * p) + 1
    hi = max(lo, (best_n + 900) // (2 * p))
    N = int(rng.integers(lo, hi + 1))
    w = COMPS[p][int(rng.integers(len(COMPS[p])))]
    MT, inv = random_metacyclic(N, rng)
    gen = anneal_gen(p, w, N, MT, inv, d, D, rng)
    return {'gen': gen, 'n': 2 * p * N, 'conv': lambda adj, p=p, N=N: (2 * p * N, edges_from_adj(adj))}


# ----------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.80 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        MT, _ = group_meta(*FALLBACK_GROUP)
        n, e = haar_edges(MT, FALLBACK_S)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    def spawn(kind):
        try:
            if kind == 'haar':
                return spawn_haar(best_n, rng, d)
            return spawn_lift(best_n, rng, d, D)
        except Exception:
            return None

    kinds = ['haar', 'lift'] * (POOL // 2)
    pool = [spawn(k) for k in kinds]

    while time.monotonic() < deadline:
        for idx in range(len(pool)):
            if time.monotonic() >= deadline:
                break
            task = pool[idx]
            kind = kinds[idx]
            if task is None or task['n'] <= best_n:
                pool[idx] = spawn(kind)
                continue
            try:
                out = next(task['gen'])
            except StopIteration:
                pool[idx] = spawn(kind)
                continue
            except Exception:
                pool[idx] = spawn(kind)
                continue
            if out is not None:
                try:
                    n, edges = task['conv'](out[1])
                    if n > best_n and lib.is_valid(n, edges, d, D):
                        best_n, best_edges = n, edges
                except Exception:
                    pass
                pool[idx] = spawn(kind)

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
