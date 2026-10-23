"""Combined search for the bipartite degree-diameter problem, d=10, D=5.

Two searches share one time budget:
  1. Haar graphs (2|G| vertices, d-regular). A set S of d group elements is valid iff
     (S^-1 S)^2 = G and (S S^-1)^2 = G. Simulated annealing on S over several non-abelian
     groups of order just above 2000, starting from a near-miss set first.
  2. Multi-orbit voltage lifts over metacyclic groups with p base A-vertices and p base
     B-vertices. Annealing on voltages, round robin over several tasks. Multiplicities are
     circulant compositions of d.

Any cost-0 candidate with more vertices than the current best is checked with lib.is_valid.
The fallback is a valid Haar graph on Z_199 x| Z_9 (3582 vertices).
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10
POOL = 5

FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
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


def group_agl(q, k=None):
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
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ----------------------------------------------------------------- Haar search (annealing on S)

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


def one_swap_scan(MT, inv, S, deadline, chunk=512):
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


def haar_search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    N = MT.shape[0]
    S0 = None if S0 is None else np.array(S0, dtype=np.int32)
    best, bestc = None, 10 ** 9
    S, cur, since = (S0.copy() if S0 is not None else None), None, 0

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


def haar_edges(MT, S):
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def run_haar(d, D, rng, deadline_all, plan):
    """Run the Haar plan with time shares; return a validated graph or None."""
    total_w = sum(w for *_, w in plan)
    for name, builder, S0, w in plan:
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = haar_search(MT, inv, d, S0, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            try:
                n, edges = haar_edges(MT, S)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                pass
    return None


# ---------------------------------------------------- multi-orbit voltage lifts (annealing)

def compositions(total, parts):
    if parts == 1:
        return [(total,)]
    out = []
    for a in range(1, total - parts + 2):
        for rest in compositions(total - a, parts - 1):
            out.append((a,) + rest)
    return out


COMPS = {p: compositions(TARGET_D, p) for p in range(1, 5)}


def layout(p, w):
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
    blocks_of = [np.nonzero((di_a == di[t]) & (dj_a == dj[t]))[0] for t in range(T)]
    return di_a, dj_a, colA, colB, blocks_of


def cost_of(adj, p, N, D):
    n = adj.shape[0]
    S = 2 * p
    src = [i * N for i in range(p)] + [(p + j) * N for j in range(p)]
    reach = np.zeros((S, n), dtype=bool)
    reach[np.arange(S), src] = True
    for _ in range(D):
        reach = reach | reach[:, adj].any(axis=2)
    return S * n - int(np.count_nonzero(reach))


def edges_from_adj(adj):
    n, dd = adj.shape
    src = np.repeat(np.arange(n, dtype=np.int64), dd)
    dst = adj.ravel()
    mask = src < dst
    return list(zip(src[mask].tolist(), dst[mask].tolist()))


def anneal_gen(p, w, N, MT, inv, d, D, rng):
    """Generator: one annealing step per yield; yields ('found', adj) at cost 0, then ends."""
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


def random_group(N, rng):
    cands = [(m, N // m) for m in range(2, N) if N % m == 0 and N // m >= 2]
    if not cands:
        return group_meta(1, N, 0 if N > 1 else 0)
    m, k = cands[int(rng.integers(len(cands)))]
    rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    r = rs[int(rng.integers(len(rs)))] if rs else 1
    return group_meta(m, k, r)


def spawn(best_n, rng, d, D):
    p = int(rng.integers(1, 5))
    lo = best_n // (2 * p) + 1
    hi = (best_n + 900) // (2 * p)
    if hi < lo:
        hi = lo
    N = int(rng.integers(lo, hi + 1))
    w = COMPS[p][int(rng.integers(len(COMPS[p])))]
    MT, inv = random_group(N, rng)
    gen = anneal_gen(p, w, N, MT, inv, d, D, rng)
    return {'gen': gen, 'n': 2 * p * N}


def multi_phase(best_n, best_edges, deadline, rng, d, D):
    pool = [spawn(best_n, rng, d, D) for _ in range(POOL)]
    while time.monotonic() < deadline:
        for idx in range(len(pool)):
            if time.monotonic() >= deadline:
                break
            task = pool[idx]
            if task['n'] <= best_n:
                pool[idx] = spawn(best_n, rng, d, D)
                continue
            try:
                out = next(task['gen'])
            except Exception:
                pool[idx] = spawn(best_n, rng, d, D)
                continue
            if out is not None:
                n = task['n']
                ok = False
                try:
                    edges = edges_from_adj(out[1])
                    ok = n > best_n and lib.is_valid(n, edges, d, D)
                except Exception:
                    ok = False
                if ok:
                    best_n, best_edges = n, edges
                pool[idx] = spawn(best_n, rng, d, D)
    return best_n, best_edges


# ----------------------------------------------------------------------------- plan and build

# (name, group builder, start set S0 or None, weight). S0 = element indices of the group table.
PLAN = [
    ('meta 401/5/39, order 2005, 6 short', lambda: group_meta(401, 5, 39),
     [0, 399, 725, 919, 893, 646, 1508, 130, 652, 957], 3),
    ('SL(2,7) x Z_6, order 2016', lambda: group_times_cyclic(group_sl2(7), 6), None, 1.5),
    ('Heis(7) x Z_6, order 2058', lambda: group_times_cyclic(group_heis(7), 6), None, 1.5),
    ('meta 336/6/17, order 2016', lambda: group_meta(336, 6, 17), None, 1),
    ('AGL(1,13) x Z_13, order 2028', lambda: group_times_cyclic(group_agl(13), 13), None, 1),
    ('AGL(1,16) x Z_9, order 2160', lambda: group_times_cyclic(group_agl(16), 9), None, 1),
]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.8 * time_limit, time_limit - 8.0))
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

    # Phase A: Haar annealing over non-abelian groups near order 2000.
    haar_deadline = t0 + 0.5 * budget
    got = run_haar(d, D, rng, haar_deadline, PLAN)
    if got is not None and got[0] > best_n:
        return got

    # Phase B: multi-orbit voltage lifts for the remaining time.
    best_n, best_edges = multi_phase(best_n, best_edges, deadline, rng, d, D)

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
