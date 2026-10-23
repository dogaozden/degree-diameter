"""Combined search for the bipartite degree-diameter problem at d=10, D=5.

Two searches share one time budget:
  1. Haar graphs over non-abelian metacyclic groups Z_m x|_lam Z_k with |G| > 2000 (so 2|G| > 4000).
     Annealing on the connection set S minimises the number of uncovered group elements.
     Cost 0 means diameter <= 5. Near-miss start sets from the parent programs are tried first.
  2. Multi-orbit voltage lifts (p base vertices per side, circulant multiplicities) annealed on voltages.

Every returned graph is checked with lib.is_valid. A valid Haar graph of order 3582 is the fallback.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10
POOL = 4

FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
NEAR_GROUP = (401, 5, 39)            # order 2005, a few elements short in earlier runs
NEAR_S0 = [0, 399, 725, 919, 893, 646, 1508, 130, 652, 957]


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
    if pow(lam, k, m) != 1 % m:
        raise ValueError("bad metacyclic parameters")
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi, None]] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def meta_candidates(lo, hi, rng, cap):
    """Random sample of (m, k, lam) with m*k in [lo, hi], non-abelian (lam != 1)."""
    items = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    items.append((m, k, lam))
    if not items:
        return []
    order = rng.permutation(len(items))[:cap]
    return [items[i] for i in order]


def random_group(N, rng):
    cands = [(m, N // m) for m in range(2, N) if N % m == 0 and N // m >= 2]
    if not cands:
        return group_meta(N, 1, 1)
    m, k = cands[int(rng.integers(len(cands)))]
    rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    r = rs[int(rng.integers(len(rs)))] if rs else 1
    return group_meta(m, k, r)


# ----------------------------------------------------------------------------- Haar search

def _cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def cost(MT, inv, S):
    N = MT.shape[0]
    Si = inv[S]
    total = 0
    for P in (MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()):
        total += N - int(_cover(MT, N, np.unique(P)).sum())
    return total


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X (only words involving slot i are recomputed)."""
    N = MT.shape[0]
    K = len(X)
    rest = np.delete(S, i)
    total = np.zeros(K, dtype=np.int64)
    offs = (np.arange(K, dtype=np.int64) * N)[:, None]
    ri = inv[rest]
    xi = inv[X]
    for side in (0, 1):
        F = np.unique(MT[ri[:, None], rest[None, :]] if side == 0 else MT[rest[:, None], ri[None, :]])
        base = _cover(MT, N, F)
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


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
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


def haar_phase(d, D, deadline, rng, floor_n):
    """Anneal Haar connection sets over candidate groups; returns the list of checked valid graphs found."""
    cands = [(3, (lambda: group_meta(*NEAR_GROUP)), NEAR_S0),
             (2, (lambda: group_meta(336, 6, 17)), None)]
    for m, k, lam in meta_candidates(2001, 2030, rng, 12):
        cands.append((1, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None))
    remaining = sum(w for w, _, _ in cands)
    best_n = floor_n
    results = []
    for w, builder, S0 in cands:
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) * w / remaining
        remaining -= w
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, S0, end, rng)
        except Exception:
            continue
        if S is None or c != 0:
            continue
        try:
            n, edges = haar_edges(MT, S)
            if n > best_n and lib.is_valid(n, edges, d, D):
                results.append((n, edges))
                best_n = n
        except Exception:
            pass
    return results


# ----------------------------------------------------------------------------- multi-orbit lifts

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
    colA, colB = [0] * T, [0] * T
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
    n, d = adj.shape
    src = np.repeat(np.arange(n, dtype=np.int64), d)
    dst = adj.ravel()
    mask = src < dst
    return list(zip(src[mask].tolist(), dst[mask].tolist()))


def anneal_gen(p, w, N, MT, inv, d, D, rng):
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


def spawn(best_n, rng, d, D):
    p = int(rng.integers(1, 5))
    lo = best_n // (2 * p) + 1
    hi = max(lo, (best_n + 900) // (2 * p))
    N = int(rng.integers(lo, hi + 1))
    w = COMPS[p][int(rng.integers(len(COMPS[p])))]
    MT, inv = random_group(N, rng)
    return {'gen': anneal_gen(p, w, N, MT, inv, d, D, rng), 'n': 2 * p * N}


def lift_phase(d, D, deadline, rng, best_n):
    best = None
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
                try:
                    edges = edges_from_adj(out[1])
                    ok = n > best_n and lib.is_valid(n, edges, d, D)
                except Exception:
                    ok = False
                if ok:
                    best_n, best = n, (n, edges)
                pool[idx] = spawn(best_n, rng, d, D)
    return best


# ----------------------------------------------------------------------------- driver

def trivial(d, D):
    """Always-valid small graph for other (d, D)."""
    options = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        options.append(lambda: lib.projective_plane_incidence(d - 1))
    options.append(lambda: lib.haar_graph(d, range(d)))
    for make in options:
        try:
            n, e = make()
            if lib.is_valid(n, e, d, D):
                return n, e
        except Exception:
            pass
    return 2, [(0, 1)]


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(3.0, min(0.75 * time_limit, time_limit - 10.0))
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

    haar_deadline = t0 + 0.55 * budget
    for n, e in haar_phase(d, D, haar_deadline, rng, best_n):
        if n > best_n:
            best_n, best_edges = n, e

    res = lift_phase(d, D, deadline, rng, best_n)
    if res is not None and res[0] > best_n:
        best_n, best_edges = res

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
