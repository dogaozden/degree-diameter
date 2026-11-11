"""Haar and multi-orbit lift search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  Let G be a finite group.  A G-invariant bipartite graph with r A-orbits and r B-orbits has vertices
(a, g) and (b, g), and edges (a, g) ~ (b, s*g) for each dart (a, b, s).  Right multiplication by any h in G
is an automorphism, so the diameter is at most 5 iff, from one representative per orbit, every vertex lies
within distance 5.  This is checked exactly with boolean reach sets.

STAGE 1 (new): r = 2 orbits per side, d/r darts per (a, b) pair, group orders in (1000, 1100].  Annealing
over the voltages with an exact reach-set cost.  A cost-0 result is built and checked with lib.is_valid.

STAGE 2 (old): the parent's Haar-graph search over groups, annealed from near-miss start sets.

FALLBACK: a valid smaller Haar graph, checked at run time.  If everything fails, trivial(d, D) is returned.
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


# ============================================================ STAGE 1: multi-orbit lift (new construction)

def _mo_darts(V):
    """Flatten the voltage array V[a, b, kk] into dart arrays (source orbit, target orbit, voltage)."""
    r, _, k = V.shape
    Da = np.repeat(np.arange(r, dtype=np.int64), r * k)
    Db = np.tile(np.repeat(np.arange(r, dtype=np.int64), k), r)
    Ds = V.reshape(-1).astype(np.int64)
    return Da, Db, Ds


def mo_cost(MT, inv, V):
    """Number of (representative, vertex) pairs at distance > 5, summed over one representative per orbit.
    Cost 0 means the lifted graph has diameter <= 5."""
    N = MT.shape[0]
    r, _, k = V.shape
    Da, Db, Ds = _mo_darts(V)
    Dsi = inv[Ds].astype(np.int64)
    TB = Db[:, None] * N + MT[Ds].astype(np.int64)     # A-vertex g -> B-vertex s*g
    TA = Da[:, None] * N + MT[Dsi].astype(np.int64)    # B-vertex h -> A-vertex s^-1*h
    total = 0
    for o in range(2 * r):
        RA = np.zeros(r * N, dtype=bool)
        RB = np.zeros(r * N, dtype=bool)
        if o < r:
            RA[o * N] = True
        else:
            RB[(o - r) * N] = True
        for _ in range(5):
            mA = RA.reshape(r, N)[Da]
            mB = RB.reshape(r, N)[Db]
            nA = RA.copy()
            nB = RB.copy()
            nB[TB[mA]] = True
            nA[TA[mB]] = True
            RA, RB = nA, nB
        total += 2 * r * N - int(RA.sum()) - int(RB.sum())
    return total


def mo_search(MT, inv, r, k, deadline, rng, patience=2500, temp=0.7):
    """Anneal the voltages V[a, b, :] (k distinct group elements per orbit pair) until cost 0 or the deadline.
    Restarts from a random V when stuck.  Returns (best V, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    while time.monotonic() < deadline:
        V = np.zeros((r, r, k), dtype=np.int64)
        for a in range(r):
            for b in range(r):
                V[a, b] = rng.choice(N, k, replace=False)
        cur = mo_cost(MT, inv, V)
        since = 0
        if cur < bestc:
            best, bestc = V.copy(), cur
        if cur == 0:
            return best, 0
        while time.monotonic() < deadline and since < patience:
            a = int(rng.integers(r))
            b = int(rng.integers(r))
            kk = int(rng.integers(k))
            s = int(rng.integers(N))
            if s in V[a, b]:
                since += 1
                continue
            old = int(V[a, b, kk])
            V[a, b, kk] = s
            c = mo_cost(MT, inv, V)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cur = c
                if cur < bestc:
                    best, bestc, since = V.copy(), cur, 0
                    if cur == 0:
                        return best, 0
                else:
                    since += 1
            else:
                V[a, b, kk] = old
                since += 1
    return best, bestc


def mo_edges(MT, V):
    """Edge list of the lift: A-vertex (a, g) = a*N + g, B-vertex (b, h) = (r + b)*N + h, edges (a,g)~(b, s*g)."""
    N = MT.shape[0]
    r, _, k = V.shape
    edges = []
    for a in range(r):
        for b in range(r):
            for kk in range(k):
                row = MT[int(V[a, b, kk])]
                for g in range(N):
                    edges.append((a * N + g, (r + b) * N + int(row[g])))
    return 2 * r * N, edges


def _isprime(n):
    return n > 1 and all(n % p for p in range(2, int(n ** 0.5) + 1))


def mo_candidates():
    """Group builders with order in (1000, 1100], smallest first.  Metacyclic groups Z_m x| Z_k (m prime) and
    some direct products of non-abelian groups with cyclic groups."""
    out = []
    for k in range(2, 13):
        for m in range(1001 // k + 1, 1100 // k + 2):
            if m * k <= 1000 or m * k > 1100:
                continue
            if not _isprime(m) or (m - 1) % k:
                continue
            lam = next((x for x in range(2, m) if pow(x, k, m) == 1), None)
            if lam is None:
                continue
            out.append((m * k, (lambda m=m, k=k, lam=lam: group_meta(m, k, lam))))
    out.append((1008, lambda: group_times_cyclic(group_agl(7), 24)))
    out.append((1080, lambda: group_times_cyclic(group_sl2(5), 9)))
    out.append((1100, lambda: group_times_cyclic(group_agl(11), 10)))
    out.append((1125, lambda: group_times_cyclic(group_heis(5), 9)))
    out.sort(key=lambda t: t[0])
    return [f for _, f in out[:8]]


def multi_orbit_stage(d, D, rng, deadline):
    """Try the multi-orbit lifts (r = 2 orbits per side) over several groups.  Returns a valid (n, edges) or None."""
    r = 2
    if d % r:
        return None
    k = d // r
    cands = mo_candidates()
    for idx, builder in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = builder()
            V, c = mo_search(MT, inv, r, k, end, rng)
        except Exception:
            continue
        if V is not None and c == 0:
            n, edges = mo_edges(MT, V)
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


# ================================================================ STAGE 2: parent's Haar-graph search

def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """(side-0 pair products S_i^-1 S_j, side-1 pair products S_i S_j^-1) as flat arrays."""
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def batch_costs(MT, inv, S, i, X):
    """cost of S with slot i replaced by x, for every x in the int array X."""
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


def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def run(d, D, seed, time_limit, plan, fallback, budget):
    """plan: list of (name, builder, S0 or None, weight); fallback: (builder, S) of a valid smaller graph.
    Spends at most `budget` seconds on the plan."""
    t0 = time.monotonic()
    deadline_all = t0 + budget
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


# ======================================================================================== cell: d10D5

TARGET = (10, 5)

PLAN = [
    ('meta 401/5/39, order 2005, 6 short', lambda: group_meta(401, 5, 39),
     [0, 399, 725, 919, 893, 646, 1508, 130, 652, 957], 4),
    ('SL(2,7) x Z_6, order 2016', lambda: group_times_cyclic(group_sl2(7), 6), None, 2),
    ('Heis(7) x Z_6, order 2058', lambda: group_times_cyclic(group_heis(7), 6), None, 2),
    ('meta 336/6/17, order 2016', lambda: group_meta(336, 6, 17), None, 1),
    ('AGL(1,13) x Z_13, order 2028', lambda: group_times_cyclic(group_agl(13), 13), None, 1),
    ('AGL(1,16) x Z_9, order 2160', lambda: group_times_cyclic(group_agl(16), 9), None, 1),
]

# Valid smaller Haar graph (order 1791, 3582 vertices), checked at run time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    total = 0.8 * time_limit
    rng = np.random.default_rng(seed)
    try:
        res = multi_orbit_stage(d, D, rng, t0 + 0.6 * total)
        if res is not None:
            return res
    except Exception:
        pass
    remaining = max(0.0, t0 + total - time.monotonic())
    return run(d, D, seed, time_limit, PLAN, FALLBACK, remaining)
