"""Bipartite degree-diameter search for (d, D) = (10, 5).

Phase 1 (bold, new): G-lifts (voltage graphs) over a 2s-vertex base (s A-vertices, s B-vertices,
DEG = 10 darts per base vertex) with a metacyclic group G of order M, so the lift has 2*s*M vertices.
Left multiplication by G is an automorphism, so the diameter is exact after BFS from the 2s base
representatives (e, U). Annealing moves voltages and base permutations; the cost is the number of
unreached (source, vertex) pairs. Any cost-0 lift with 2*s*M >= 4002 is checked with lib.is_valid.

Phase 2 (parent): Haar-graph annealing over metacyclic groups (order >= 1792). Fallback: a stored
valid Haar graph. Every returned graph passes lib.is_valid; other cases return a small checked graph.
"""
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


def metacyclic_orders(lo, hi):
    """(N, m, k, lam) with N = m*k in [lo, hi], k >= 2, m >= 3, lam a nontrivial unit with lam^k = 1 mod m."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((N, m, k, lam))
    return out


# ------------------------------------------------------------------------ phase 1: voltage lifts

DEG = 10
DIAM = 5
LIFT_FRAC = 0.6       # share of the budget given to the lift phase
SLICE_LIFT = 3.0      # seconds per group in the lift phase


def lift_anneal(MT, inv, s, rng, deadline):
    """Anneal voltages (and base permutations) of a 2s-vertex-per-side lift over the group (MT, inv).
    Returns (n, edges) if a checked valid graph is found before the deadline, else None."""
    M = MT.shape[0]
    n = 2 * s * M
    srcs = [U * M for U in range(2 * s)]          # identity-element representatives of each base vertex
    ar = np.arange(M)
    tt = np.arange(DEG)

    def nbr_of(P, V):
        # A-vertex (x, A_i) has dart t to (x*V[t,i], B_{P[t,i]}).
        # B-vertex (y, B_j) has dart t to (y*V^-1, A_i) where i = Pinv[t, j].
        Pinv = np.argsort(P, axis=1)
        NA = np.empty((s, M, DEG), dtype=np.int64)
        for i in range(s):
            NA[i] = MT[ar[:, None], V[:, i][None, :]] + ((s + P[:, i]) * M)[None, :]
        NB = np.empty((s, M, DEG), dtype=np.int64)
        for j in range(s):
            ii = Pinv[:, j]
            vv = V[tt, ii]
            NB[j] = MT[ar[:, None], inv[vv][None, :]] + (ii * M)[None, :]
        return np.concatenate([NA.reshape(s * M, DEG), NB.reshape(s * M, DEG)])

    def cost_of(nb):
        total = 0
        for src in srcs:
            vis = np.zeros(n, dtype=bool)
            vis[src] = True
            fr = np.array([src], dtype=np.int64)
            for _ in range(DIAM):
                cand = nb[fr].ravel()
                cand = cand[~vis[cand]]
                if cand.size == 0:
                    break
                cand = np.unique(cand)
                vis[cand] = True
                fr = cand
            total += n - int(vis.sum())
        return total

    def fresh():
        P = np.array([rng.permutation(s) for _ in range(DEG)], dtype=np.int64)
        V = rng.integers(0, M, size=(DEG, s)).astype(np.int64)
        return P, V

    P, V = fresh()
    nb = nbr_of(P, V)
    cur = cost_of(nb)
    since = 0
    temp = 0.5
    while cur > 0 and time.monotonic() < deadline:
        P0, V0 = P.copy(), V.copy()
        if rng.random() < 0.15:
            t = int(rng.integers(DEG))
            a, b = rng.choice(s, 2, replace=False)
            P[t, a], P[t, b] = P[t, b], P[t, a]
        else:
            t = int(rng.integers(DEG))
            i = int(rng.integers(s))
            V[t, i] = rng.integers(M)
        nb2 = nbr_of(P, V)
        c2 = cost_of(nb2)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur, nb = c2, nb2
            since = 0 if delta < 0 else since + 1
        else:
            P, V = P0, V0
            since += 1
        if since > 3000:
            P, V = fresh()
            nb = nbr_of(P, V)
            cur = cost_of(nb)
            since = 0
    if cur != 0:
        return None
    edges = set()
    for u in range(s * M):
        for v in nb[u]:
            v = int(v)
            edges.add((u, v) if u < v else (v, u))
    edges = sorted(edges)
    if lib.is_valid(n, edges, DEG, DIAM):
        return n, edges
    return None


def run_lift(rng, deadline):
    """Round-robin over lift groups for base sizes s = 2, 3, 4 with 2*s*M >= 4002.  Returns a checked graph or None."""
    specs = []
    for s in (2, 3, 4):
        lo = -(-4002 // (2 * s))
        hi = lo + 40
        for (N, m, k, lam) in metacyclic_orders(lo, hi):
            specs.append((s, m, k, lam))
    if not specs:
        return None
    rng.shuffle(specs)
    idx = 0
    while time.monotonic() < deadline - 0.5:
        s, m, k, lam = specs[idx % len(specs)]
        idx += 1
        slice_end = min(deadline, time.monotonic() + SLICE_LIFT)
        try:
            MT, inv = group_meta(m, k, lam)
            g = lift_anneal(MT, inv, s, rng, slice_end)
        except Exception:
            continue
        if g is not None:
            return g
    return None


# ------------------------------------------------------------------------ phase 2: Haar search

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


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
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
    """Always-valid small graph for any other (d, D); every candidate is checked."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        g = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(g[0], g[1], d, D):
            return g
    if D >= 2 and d >= 1:
        g = (2 * d, [(i, d + j) for i in range(d) for j in range(d)])
        if lib.is_valid(g[0], g[1], d, D):
            return g
    if d >= 1 and D >= 1:
        return 2, [(0, 1)]
    return 1, []


TARGET = (10, 5)
LO, HI = 1792, 2100
SLICE = 4.0
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def run_meta(d, D, rng, deadline):
    keyed = {}
    for c in metacyclic_orders(LO, HI):
        keyed.setdefault(c[0], []).append(c)
    order = []
    for N in sorted(keyed):
        grp = keyed[N]
        rng.shuffle(grp)
        order.extend(grp)

    idx = 0
    while order and time.monotonic() < deadline - 0.5:
        now = time.monotonic()
        slice_end = min(deadline, now + SLICE)
        _, m, k, lam = order[idx % len(order)]
        idx += 1
        try:
            MT, inv = group_meta(m, k, lam)
            S, c = search(MT, inv, d, slice_end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g

    try:
        MT, _ = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        t0 = time.monotonic()
        end = t0 + 0.85 * time_limit
        rng = np.random.default_rng(seed)
        lift_end = t0 + LIFT_FRAC * 0.85 * time_limit
        g = run_lift(rng, lift_end)
        if g is not None:
            return g
        return run_meta(d, D, rng, end)
    except Exception:
        return trivial(d, D)
