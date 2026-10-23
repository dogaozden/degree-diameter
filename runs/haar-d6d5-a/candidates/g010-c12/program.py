"""Two-stage search for the bipartite degree-diameter problem at diameter 5 (numpy only).

Stage 1 (new, high-risk): G-semiregular voltage lifts with r base vertices per side.
A-fibre i and B-fibre j are joined by M[i][j] darts with group voltages s, so
(g, A_i) ~ (s*g, B_j). Pattern row and column sums are 6, so the graph is 6-regular on
2*r*|G| vertices. Right multiplication by G is an automorphism that is transitive on each
fibre, so the diameter equals the maximum eccentricity over the 2r fibre roots (1, X).
Annealing minimises the number of (root, vertex) pairs at distance > 5. Groups of order
just above the threshold (r=2: |G| >= 172; r=3: |G| >= 115) would beat the record of 684.

Stage 2 (parent, unchanged in spirit): Haar-graph search over non-abelian groups, with its
order-342 safety net and an order-330 fallback.

Every candidate is checked with lib.is_valid before it is returned, so a bug can only lose
score, never produce an invalid graph.
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
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)   # (0,0,0) is first

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


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


def metacyclic_candidates(lo, hi, per_pair, limit):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with lo <= m*k <= hi (up to per_pair lam values per (m, k))."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            cnt = 0
            for lam in range(2, m):
                if lam % m != 1 and math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((N, m, k, lam))
                    cnt += 1
                    if cnt >= per_pair:
                        break
            if len(out) >= limit:
                return out
    return out


# ============================================================ stage 1: G-semiregular voltage lifts

def pattern_darts(r, M):
    """Expand a r x r multiplicity matrix into dart lists (di, dj): one entry per dart."""
    di, dj = [], []
    for i in range(r):
        for j in range(r):
            for _ in range(M[i][j]):
                di.append(i)
                dj.append(j)
    return di, dj


def build_nb(MT, inv, r, N, di, dj, ds, a_idx, b_idx):
    """Neighbour table (V, 6) of the lift. A-vertex (g, A_i) has id i*N+g; B-vertex (h, B_j) has id r*N + j*N + h."""
    V = 2 * r * N
    d = len(a_idx[0])
    NB = np.empty((V, d), dtype=np.int64)
    for i in range(r):
        for c, k in enumerate(a_idx[i]):
            # (g, A_i) ~ (s*g, B_j)
            NB[i * N:(i + 1) * N, c] = r * N + dj[k] * N + MT[int(ds[k])]
    for j in range(r):
        for c, k in enumerate(b_idx[j]):
            # (h, B_j) ~ (g, A_i) with s*g = h, so g = s^-1 * h
            NB[r * N + j * N:r * N + (j + 1) * N, c] = di[k] * N + MT[int(inv[int(ds[k])])]
    return NB


def lift_cost(NB, roots, V, D):
    """Total number of (root, vertex) pairs at distance > D from each root. Zero iff diameter <= D."""
    total = 0
    for v in roots:
        vis = np.zeros(V, dtype=bool)
        vis[v] = True
        fr = np.array([v], dtype=np.int64)
        for _ in range(D):
            m = np.zeros(V, dtype=bool)
            m[NB[fr].ravel()] = True
            m &= ~vis
            fr = np.flatnonzero(m)
            if fr.size == 0:
                break
            vis[fr] = True
        total += V - int(vis.sum())
    return total


def lift_search(MT, inv, r, M, deadline, rng, D=5, patience=2500, temp=0.8):
    """Anneal dart voltages to minimise lift_cost. Returns (best voltages, best cost)."""
    N = MT.shape[0]
    di, dj = pattern_darts(r, M)
    K = len(di)
    a_idx = [[k for k in range(K) if di[k] == i] for i in range(r)]
    b_idx = [[k for k in range(K) if dj[k] == j] for j in range(r)]
    pair_ks = {}
    for k in range(K):
        pair_ks.setdefault((di[k], dj[k]), []).append(k)
    roots = [i * N for i in range(r)] + [r * N + j * N for j in range(r)]
    V = 2 * r * N

    def evaluate(ds):
        return lift_cost(build_nb(MT, inv, r, N, di, dj, ds, a_idx, b_idx), roots, V, D)

    best, bestc = None, 10 ** 9
    while time.monotonic() < deadline:
        ds = np.zeros(K, dtype=np.int64)
        for key, ks in pair_ks.items():   # distinct voltages inside each (i, j) bundle
            vals = rng.choice(N, len(ks), replace=False)
            for k, v in zip(ks, vals):
                ds[k] = int(v)
        cur = evaluate(ds)
        if cur < bestc:
            best, bestc = ds.copy(), cur
        since = 0
        while time.monotonic() < deadline and since < patience:
            if cur == 0:
                return ds.copy(), 0
            k = int(rng.integers(K))
            key = (di[k], dj[k])
            others = [int(ds[q]) for q in pair_ks[key] if q != k]
            x = int(rng.integers(N))
            if x in others:
                since += 1
                continue
            old = int(ds[k])
            ds[k] = x
            c = evaluate(ds)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cur = c
                if cur < bestc:
                    best, bestc = ds.copy(), cur
                since = 0 if delta < 0 else since + 1
            else:
                ds[k] = old
                since += 1
        if cur == 0:
            return ds.copy(), 0
    return best, bestc


def lift_graph(MT, r, N, di, dj, ds):
    """Edges of the lift: (g, A_i) ~ (s*g, B_j) for every dart (i, j, s)."""
    n = 2 * r * N
    edges = []
    for k in range(len(ds)):
        i, j = di[k], dj[k]
        row = MT[int(ds[k])]
        for g in range(N):
            edges.append((i * N + g, r * N + j * N + int(row[g])))
    return n, edges


def run_lift(D, seed, deadline, plan):
    """Round-robin lift searches over the plan until deadline. Returns a validated (n, edges) or None."""
    rng = np.random.default_rng(seed)
    cache = {}
    slice_len = 0.5
    while time.monotonic() < deadline - 0.05:
        for idx, (name, builder, r, M) in enumerate(plan):
            now = time.monotonic()
            if now >= deadline:
                break
            if idx not in cache:
                try:
                    cache[idx] = builder()
                except Exception:
                    cache[idx] = None
            if cache[idx] is None:
                continue
            MT, inv = cache[idx]
            end = min(deadline, now + slice_len)
            try:
                ds, c = lift_search(MT, inv, r, M, end, rng, D=D)
            except Exception:
                continue
            if ds is not None and c == 0:
                try:
                    di, dj = pattern_darts(r, M)
                    n, edges = lift_graph(MT, r, MT.shape[0], di, dj, ds)
                    if lib.is_valid(n, edges, 6, D):
                        return n, edges
                except Exception:
                    pass
        slice_len = min(slice_len * 1.5, 6.0)
    return None


PAT2A = [[3, 3], [3, 3]]
PAT2B = [[4, 2], [2, 4]]
PAT3 = [[3, 2, 1], [2, 1, 3], [1, 3, 2]]

LIFT_PLAN = []
for _N, _m, _k, _lam in metacyclic_candidates(172, 180, 2, 6):
    for _M in (PAT2A, PAT2B):
        LIFT_PLAN.append((f"lift r=2, Z_{_m} x| Z_{_k} (lam={_lam}), order {_N}",
                          (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam)), 2, _M))
LIFT_PLAN.append(("lift r=2, AGL(1,3) x Z_29, order 174",
                  (lambda: group_times_cyclic(group_agl(3), 29)), 2, PAT2A))
LIFT_PLAN.append(("lift r=2, AGL(1,5) x Z_9, order 180",
                  (lambda: group_times_cyclic(group_agl(5), 9)), 2, PAT2A))
for _N, _m, _k, _lam in metacyclic_candidates(115, 124, 2, 3):
    LIFT_PLAN.append((f"lift r=3, Z_{_m} x| Z_{_k} (lam={_lam}), order {_N}",
                      (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam)), 3, PAT3))


# ============================================================ stage 2: Haar-graph search (parent)

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    Si = inv[S]
    P0 = np.unique(MT[Si[:, None], S[None, :]].ravel())
    P1 = np.unique(MT[S[:, None], Si[None, :]].ravel())
    return (N - int(_cover(MT, N, P0).sum())) + (N - int(_cover(MT, N, P1).sum()))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by x, for every x in X (only slot-i words are recomputed)."""
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


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Simulated-annealing style local search over d-subsets of the group, with restarts when stuck.
    Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    while time.monotonic() < deadline:
        if S is None:
            S = random_set()
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
    """plan: list of (name, builder); candidates are time-sliced round-robin with growing slices.
    fallback: (builder, S) of a valid smaller Haar graph."""
    t0 = time.monotonic()
    deadline = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    cache = {}
    slice_len = 0.5
    while time.monotonic() < deadline - 0.05:
        for idx, (name, builder) in enumerate(plan):
            now = time.monotonic()
            if now >= deadline:
                break
            if idx not in cache:
                try:
                    cache[idx] = builder()
                except Exception:
                    cache[idx] = None
            if cache[idx] is None:
                continue
            MT, inv = cache[idx]
            end = min(deadline, now + slice_len)
            try:
                S, c = search(MT, inv, d, end, rng)
            except Exception:
                continue
            if S is not None and c == 0:
                g = checked(MT, S, d, D)
                if g is not None:
                    return g
        slice_len = min(slice_len * 1.5, 6.0)
    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ======================================================================================== cell: d6D5
TARGET = (6, 5)

PLAN = [
    ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13)),
    ('Heis(7), order 343', lambda: group_heis(7)),
    ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5)),
    ('AGL(1,5) x Z_18, order 360', lambda: group_times_cyclic(group_agl(5), 18)),
]
for _N, _m, _k, _lam in metacyclic_candidates(343, 372, 2, 28):
    PLAN.append((f"Z_{_m} x| Z_{_k} (lam={_lam}), order {_N}",
                 (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam))))
for _N, _m, _k, _lam in metacyclic_candidates(342, 342, 2, 4):
    PLAN.append((f"Z_{_m} x| Z_{_k} (lam={_lam}), order {_N}",
                 (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam))))

FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    # Stage 1: new voltage-lift search, with about half the budget.
    try:
        g = run_lift(D, seed, t0 + 0.5 * time_limit, LIFT_PLAN)
        if g is not None:
            return g
    except Exception:
        pass
    # Stage 2: the parent Haar search for the rest of the budget (ends near 0.85 * time_limit).
    elapsed = time.monotonic() - t0
    remaining = max(1.0, 0.85 * time_limit - elapsed)
    return run(d, D, seed, remaining / 0.8, PLAN, FALLBACK)
