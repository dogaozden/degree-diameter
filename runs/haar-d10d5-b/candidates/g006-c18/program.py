"""Combined search for the bipartite degree-diameter problem at d=10, D=5.

Two constructions share one time budget:
  1. Haar graphs over metacyclic groups Z_m x|_r Z_k.  A near-miss set in Z_401 x| Z_5
     (order 2005, so a valid graph would have 4010 vertices) is annealed first.
  2. Multi-orbit voltage lifts with p base vertices per side and circulant multiplicities.
     Random metacyclic groups are annealed on voltages with a round-robin pool.

Only graphs that pass lib.is_valid are returned. A verified Haar fallback (3582 vertices)
is used whenever nothing better is found. Other (d, D) cases get a small always-valid graph.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10
POOL = 5

HAAR_GROUP = (401, 5, 39)
HAAR_S0 = [0, 399, 725, 919, 893, 646, 1508, 130, 652, 957]

FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------ groups

def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l). Returns (MT, inv)."""
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    ak = idx // k
    jk = idx % k
    MT = np.empty((N, N), dtype=np.int32)
    step = 128
    for lo in range(0, N, step):
        hi = min(N, lo + step)
        a = ak[lo:hi, None]
        j = jk[lo:hi, None]
        MT[lo:hi] = ((a + pw[j] * ak[None, :]) % m) * k + (j + jk[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def random_group(N, rng):
    """A random metacyclic group of order N, non-abelian when possible."""
    cands = [(m, N // m) for m in range(2, N) if N % m == 0 and N // m >= 2]
    if not cands:
        return group_table(1, N, 1)  # cyclic
    m, k = cands[int(rng.integers(len(cands)))]
    rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    r = rs[int(rng.integers(len(rs)))] if rs else 1
    return group_table(m, k, r)


def compositions(total, parts):
    """All ways to write total as an ordered sum of `parts` positive integers."""
    if parts == 1:
        return [(total,)]
    out = []
    for a in range(1, total - parts + 2):
        for rest in compositions(total - a, parts - 1):
            out.append((a,) + rest)
    return out


COMPS = {p: compositions(TARGET_D, p) for p in range(1, 5)}


# ------------------------------------------------------------------- Haar graph search

def _cover(MT, N, P):
    """Boolean array of elements covered by the pair products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements on both sides (0 = valid diameter-5 Haar graph)."""
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


def one_swap_scan(MT, inv, S, deadline, chunk=512):
    """Score every single-slot replacement of S. Returns (best cost, best S)."""
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


def random_set(N, d, rng):
    return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Anneal a d-subset of the group. Starts from S0 after a 1-swap scan, restarts when stuck.
    Returns (best S, best cost)."""
    N = MT.shape[0]
    S0 = np.array(S0, dtype=np.int32)
    best = S0.copy()
    bestc = cost(MT, inv, S0)
    if bestc == 0:
        return best, 0
    S = None
    rem = max(0.0, deadline - time.monotonic())
    c1, S1 = one_swap_scan(MT, inv, S0, time.monotonic() + 0.25 * rem)
    if S1 is not None and c1 < bestc:
        best, bestc, S = S1.copy(), c1, S1.copy()
        if c1 == 0:
            return best, 0
    cur, since = None, 0
    while time.monotonic() < deadline:
        if S is None:
            if rng.random() < 0.5:
                S = S0.copy()
                for i in rng.choice(d, 2, replace=False):
                    S[i] = rng.integers(N)
                if len(set(S.tolist())) < d:
                    S = random_set(N, d, rng)
            else:
                S = random_set(N, d, rng)
            cur = None
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
    """Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


# ----------------------------------------------------------- multi-orbit voltage lifts

def layout(p, w):
    """Dart layout for the circulant base: row i, column j, and slot positions per dart."""
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
    """Number of (source, vertex) pairs at distance > D. Sources are the 2p base identities."""
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
    """Generator: one annealing step per yield. Yields ('found', adj) at cost 0, then ends."""
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
    """A fresh lift search task whose graph has more than best_n vertices."""
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


# ------------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(3.0, min(0.80 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None

    # Verified Haar fallback, so the output is never worse than 3582.
    try:
        MT, _ = group_table(*FALLBACK_GROUP)
        n, e = haar_edges(MT, FALLBACK_S)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    # Phase 1: anneal the Haar near miss in Z_401 x| Z_5 (order 2005 -> 4010 vertices if valid).
    phase1_end = t0 + 0.40 * budget
    try:
        MT, inv = group_table(*HAAR_GROUP)
        S, c = search(MT, inv, d, HAAR_S0, phase1_end, rng)
        if c == 0:
            n, e = haar_edges(MT, S)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_edges = n, e
    except Exception:
        pass

    # Phase 2: multi-orbit voltage lifts, round-robin over a pool of annealing tasks.
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
            except StopIteration:
                pool[idx] = spawn(best_n, rng, d, D)
                continue
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
                    best_n, best_edges = n, edges
                pool[idx] = spawn(best_n, rng, d, D)

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
