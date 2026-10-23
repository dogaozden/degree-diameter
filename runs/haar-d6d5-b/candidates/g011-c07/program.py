"""Two-tier search for the bipartite degree-diameter problem (numpy only).

Tier 1 (new): voltage lifts of a 2+2-vertex base graph over metacyclic groups of order N in 172..200.
The lift has 4N vertices (> 684 for N >= 172), is 6-regular and bipartite, and is checked directly with
BFS from one vertex of each base class (left multiplication is an automorphism, so this is exact).

Tier 2 (parent): Haar-graph annealing over several groups, the parent's near-miss and random plan.

Fallback: a checked smaller Haar graph, and finally a trivial always-valid graph.
Every returned graph passes lib.is_valid.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)


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
    """Table of a group given as an (N, c) coordinate array (element 0 is the identity) and a vectorised product."""
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


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


# ------------------------------------------------------------------------------ Haar-graph search (parent)

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


def haar_edges(MT, S):
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def meta_candidates(lo, hi, exclude, limit):
    """Metacyclic Z_m x|_lam Z_k (non-abelian) with order N in (lo, hi], largest orders first."""
    out = []
    for N in range(hi, lo, -1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 and (m, k, lam) not in exclude:
                    out.append((m, k, lam))
                    if len(out) >= limit:
                        return out
    return out


def run(d, D, seed, time_limit, plan, fallback):
    t0 = time.monotonic()
    deadline_all = t0 + 0.85 * time_limit
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


# ------------------------------------------------------------- new tier: 2+2 base voltage lifts (d = 6, D = 5)

K_LIFT = 4        # candidate voltage changes per step (best of K)
TEMP_LIFT = 1.0
PATIENCE_LIFT = 1500


def lift_adj(MT, inv, darts):
    """Adjacency (4N, 6) of the lift. Vertex id = class*N + x; classes 0,1 are A-side, 2,3 are B-side.
    Dart (a, b, g) joins (a, x) to (b, x*g)."""
    N = MT.shape[0]
    xs = np.arange(N)
    adj = np.empty((4 * N, 6), dtype=np.int64)
    cnt = [0, 0, 0, 0]
    for a, b, g in darts:
        ca = cnt[a]
        cnt[a] += 1
        adj[a * N:(a + 1) * N, ca] = b * N + MT[xs, g]
        cb = cnt[b]
        cnt[b] += 1
        adj[b * N:(b + 1) * N, cb] = a * N + MT[xs, inv[g]]
    return adj


def lift_cost(adj, N):
    """Uncovered (class-source, vertex) pairs at distance > 5. Zero iff the lift has diameter <= 5.
    Left multiplication is an automorphism, so one BFS per base class is exact."""
    V = 4 * N
    total = 0
    for c in range(4):
        seen = np.zeros(V, dtype=bool)
        src = c * N
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(5):
            nxt = adj[frontier].ravel()
            nxt = np.unique(nxt[~seen[nxt]])
            if nxt.size == 0:
                break
            seen[nxt] = True
            frontier = nxt
        total += V - int(seen.sum())
    return total


def lift_edges(MT, darts, N):
    xs = np.arange(N)
    edges = []
    for a, b, g in darts:
        col = MT[xs, g]
        edges.extend((a * N + x, b * N + int(col[x])) for x in range(N))
    return 4 * N, edges


def lift_search(MT, inv, rng, end):
    """Anneal voltages on the 2+2 base graph: classes A0,A1,B2,B3 with multiplicities
    t (A0-B2, A1-B3) and 6-t (A0-B3, A1-B2). Voltages within each class pair are distinct."""
    N = MT.shape[0]
    while time.monotonic() < end:
        t = int(rng.choice([2, 3, 4]))
        pairs = [(0, 2, t), (1, 3, t), (0, 3, 6 - t), (1, 2, 6 - t)]
        darts = []
        for a, b, m in pairs:
            for g in rng.choice(N, m, replace=False):
                darts.append([a, b, int(g)])
        cur = lift_cost(lift_adj(MT, inv, darts), N)
        since = 0
        while time.monotonic() < end and since < PATIENCE_LIFT:
            if cur == 0:
                n, edges = lift_edges(MT, darts, N)
                if lib.is_valid(n, edges, 6, 5):
                    return n, edges
                break
            i = int(rng.integers(len(darts)))
            a, b, _ = darts[i]
            used = {darts[j][2] for j in range(len(darts))
                    if j != i and darts[j][0] == a and darts[j][1] == b}
            best = None
            for _ in range(K_LIFT):
                g = int(rng.integers(N))
                if g in used:
                    continue
                trial = [row[:] for row in darts]
                trial[i][2] = g
                c = lift_cost(lift_adj(MT, inv, trial), N)
                if best is None or c < best[0]:
                    best = (c, g)
            if best is None:
                continue
            delta = best[0] - cur
            if delta <= 0 or rng.random() < math.exp(-delta / TEMP_LIFT):
                darts[i][2] = best[1]
                if delta < 0:
                    since = 0
                cur = best[0]
            since += 1
    return None


def lift_tier(rng, deadline):
    """Metacyclic groups with 4N > 684 (N in 172..200), one per order, largest order first."""
    cands = meta_candidates(171, 200, set(), 60)
    seen_N, groups = set(), []
    for m, k, lam in cands:
        N = m * k
        if N in seen_N:
            continue
        seen_N.add(N)
        groups.append((m, k, lam))
    groups = groups[:8]
    for idx, (m, k, lam) in enumerate(groups):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(groups) - idx)
        try:
            MT, inv = group_meta(m, k, lam)
            res = lift_search(MT, inv, rng, end)
        except Exception:
            continue
        if res is not None:
            return res
    return None


# ------------------------------------------------------------------------------ plans (parent)

PLAN = [
    ('meta 117/3/16, order 351, 2 short', lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21], 4),
    ('meta 71/5/5, order 355, 2 short', lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88], 4),
    ('SL(2,5) x Z_3, order 360, 4 short', lambda: group_times_cyclic(group_sl2(5), 3), [0, 246, 216, 211, 99, 132], 3),
]


def _extra_plan():
    used = {(117, 3, 16), (71, 5, 5)}
    entries = []
    for m, k, lam in meta_candidates(330, 342, used, 6):
        entries.append((f'meta {m}/{k}/{lam} random', (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 2))
    return entries


FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = 0.8 * time_limit
    rng = np.random.default_rng(seed)

    # Tier 1: 2+2-vertex base voltage lifts, orders 4N > 684.
    try:
        res = lift_tier(rng, t0 + 0.4 * budget)
        if res is not None:
            n, edges = res
            if lib.is_valid(n, edges, d, D):
                return n, edges
    except Exception:
        pass

    # Tier 2: parent's Haar-graph plan, then fallback.
    end = t0 + 0.9 * budget
    now = time.monotonic()
    tl2 = max(1e-3, (end - now) / 0.85)
    try:
        return run(d, D, seed, tl2, PLAN + _extra_plan(), FALLBACK)
    except Exception:
        return trivial(d, D)
