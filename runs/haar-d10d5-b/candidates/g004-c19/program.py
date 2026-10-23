"""Combined search for the bipartite degree-diameter problem at d=10, D=5.

Two constructions share one time budget:

1. Haar graphs from a non-abelian group G of order N > 1791, giving 2N > 3582 vertices. A connection set S of
   10 group elements is annealed until (S^-1 S)^2 = G and (S S^-1)^2 = G, which is exactly diameter <= 5.
   Groups are tried largest first, and the first valid result wins this phase.
2. Multi-orbit voltage lifts with p base vertices per side (p = 1..4) over random metacyclic groups.
   This generalises the Haar case, and the annealing cost counts unreached (source, vertex) pairs.

Every returned graph is checked with lib.is_valid. A valid Haar graph of 3582 vertices is the fallback.
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


# ------------------------------------------------------------------------------ group tables

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_table(m, k, r):
    """Z_m x|_r Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l). Returns (MT, inv)."""
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    ak = idx // k
    jk = idx % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 128):
        hi = min(N, lo + 128)
        a = ak[lo:hi, None]
        j = jk[lo:hi, None]
        MT[lo:hi] = ((a + pw[j] * ak[None, :]) % m) * k + (j + jk[None, :]) % k
    return _finish(MT)


def random_group(N, rng):
    """A random metacyclic group of order N, non-abelian when possible."""
    cands = [(m, N // m) for m in range(2, N) if N % m == 0 and N // m >= 2]
    if not cands:
        return group_table(1, N, 1)
    m, k = cands[int(rng.integers(len(cands)))]
    rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    r = rs[int(rng.integers(len(rs)))] if rs else 1
    return group_table(m, k, r)


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
    """Heisenberg group mod p, order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p), order p(p^2-1)."""
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
    """GF(q) x| C_k (default AGL(1, q))."""
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
    """Direct product of a table group with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------ Haar search

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


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Annealing over d-subsets of the group, with restarts. Returns (S, cost), cost 0 means valid."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    while time.monotonic() < deadline:
        if S is None:
            S = random_set()
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


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


# Largest group orders first; 2|G| vertices each. The first valid one wins the phase.
PLAN = [
    ('Heis(7) x Z_6, order 2058', lambda: group_times_cyclic(group_heis(7), 6), 2),
    ('AGL(1,13) x Z_13, order 2028', lambda: group_times_cyclic(group_agl(13), 13), 2),
    ('SL(2,7) x Z_6, order 2016', lambda: group_times_cyclic(group_sl2(7), 6), 2),
    ('AGL(1,16) x Z_8, order 1920', lambda: group_times_cyclic(group_agl(16), 8), 2),
    ('AGL(1,11) x Z_17, order 1870', lambda: group_times_cyclic(group_agl(11), 17), 2),
]


def haar_phase(d, D, rng, deadline, best):
    """Try PLAN in order within the deadline. Updates best=[n, edges] and returns True on success."""
    total_w = float(sum(w for _, _, w in PLAN))
    for name, builder, w in PLAN:
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, end, rng)
        except Exception:
            continue
        if S is not None and c == 0 and 2 * MT.shape[0] > best[0]:
            try:
                g = checked(MT, S, d, D)
            except Exception:
                g = None
            if g is not None:
                best[0], best[1] = g
                return True
    return False


# ------------------------------------------------------------- multi-orbit voltage lifts

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
    """Unreached (source, vertex) pairs; sources are the 2p base identities (right action is an automorphism)."""
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
    """A fresh multi-orbit search task whose graph has more than best_n vertices."""
    p = int(rng.integers(1, 5))
    lo = best_n // (2 * p) + 1
    hi = max(lo, (best_n + 900) // (2 * p))
    N = int(rng.integers(lo, hi + 1))
    w = COMPS[p][int(rng.integers(len(COMPS[p])))]
    MT, inv = random_group(N, rng)
    gen = anneal_gen(p, w, N, MT, inv, d, D, rng)
    return {'gen': gen, 'n': 2 * p * N}


def orbit_phase(d, D, rng, deadline, best):
    """Round-robin multi-orbit annealing until the deadline. Updates best=[n, edges] on valid finds."""
    pool = [spawn(best[0], rng, d, D) for _ in range(POOL)]
    while time.monotonic() < deadline:
        for idx in range(len(pool)):
            if time.monotonic() >= deadline:
                break
            task = pool[idx]
            if task['n'] <= best[0]:
                pool[idx] = spawn(best[0], rng, d, D)
                continue
            try:
                out = next(task['gen'])
            except Exception:
                pool[idx] = spawn(best[0], rng, d, D)
                continue
            if out is not None:
                n = task['n']
                try:
                    edges = edges_from_adj(out[1])
                    ok = n > best[0] and lib.is_valid(n, edges, d, D)
                except Exception:
                    ok = False
                if ok:
                    best[0], best[1] = n, edges
                pool[idx] = spawn(best[0], rng, d, D)


# ------------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.80 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = [0, None]
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        N = m * k
        ar = np.arange(N, dtype=np.int64)
        edges = []
        for s in FALLBACK_S:
            edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
        if lib.is_valid(2 * N, edges, d, D):
            best = [2 * N, edges]
    except Exception:
        pass

    try:
        haar_phase(d, D, rng, t0 + 0.55 * budget, best)
    except Exception:
        pass

    try:
        orbit_phase(d, D, rng, deadline, best)
    except Exception:
        pass

    if best[1] is None:
        return trivial(d, D)
    return best[0], best[1]
