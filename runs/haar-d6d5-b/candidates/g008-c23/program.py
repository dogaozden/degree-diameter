"""Voltage-lift search plus Haar near-miss search for the bipartite degree-diameter problem (numpy only).

TARGET (d=6, D=5): search over multi-orbit lifts of small bipartite base multigraphs. Base has a A-vertices and
a B-vertices, each of degree 6. Each dart (u, v, x) with a group voltage x in G gives edges (u, g) ~ (v, x*g).
Right multiplication is an automorphism, so eccentricities are constant on each base orbit. Diameter <= 5 iff
the ball of radius 5 around (u, e) covers the lift for every base vertex. Cost = number of uncovered vertices
summed over those 2a sources. Annealing on voltages finds cost 0 for lifts with 2aN > 684 vertices.

After that, a Haar near-miss search (metacyclic groups, 2-short starts) runs for the remaining time.
Every returned graph is checked with lib.is_valid. A valid smaller Haar graph is the fallback.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
DEG = 6
DIAM = 5


# ----------------------------------------------------------------------------------------- group tables

def meta_table(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> index a*k + j, (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m.
    Returns (MT, inv) with MT[x, y] = x*y and identity 0."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = ((a[:, None] + pw[j][:, None] * a[None, :]) % m) * k + (j[:, None] + j[None, :]) % k
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def meta_groups(N, limit):
    """Metacyclic groups of order N: non-abelian first, then abelian. Each is (m, k, lam)."""
    nonab, ab = [], []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k == 1:
            ab.append((m, 1, 1))
            continue
        for lam in range(1, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                (nonab if lam != 1 else ab).append((m, k, lam))
    return (nonab + ab)[:limit]


# ------------------------------------------------------------------------------- voltage lift search

def lift_nbr(a, N, MT, inv, U, W, X):
    """Neighbour array (V x DEG). A-base u, element g -> u*N+g. B-base v, element h -> (a+v)*N+h.
    Dart d = (U[d], W[d], X[d]) gives (u,g) ~ (v, X*g)."""
    V = 2 * a * N
    nbr = np.empty((V, DEG), dtype=np.int64)
    for u in range(a):
        ds = np.nonzero(U == u)[0]
        for t, d in enumerate(ds):
            nbr[u * N:(u + 1) * N, t] = (a + W[d]) * N + MT[X[d]]
    for v in range(a):
        ds = np.nonzero(W == v)[0]
        for t, d in enumerate(ds):
            nbr[(a + v) * N:(a + v + 1) * N, t] = U[d] * N + MT[inv[X[d]]]
    return nbr


def lift_cost(nbr, V, sources, D=DIAM):
    """Uncovered vertices summed over the BFS balls of radius D around each source."""
    total = 0
    for s in sources:
        vis = np.zeros(V, dtype=bool)
        vis[s] = True
        fr = np.array([s], dtype=np.int64)
        for _ in range(D):
            nb = nbr[fr].ravel()
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            fr = np.unique(nb)
            vis[fr] = True
        total += V - int(vis.sum())
    return total


def lift_search(a, N, MT, inv, deadline, rng, temp=1.5, patience=800):
    """Anneal voltages over random base structures until cost 0 or the deadline.
    Returns ((U, W, X) or None, best cost)."""
    E = DEG * a
    U = np.repeat(np.arange(a), DEG)
    sources = [u * N for u in range(a)] + [(a + v) * N for v in range(a)]
    V = 2 * a * N
    best, bestc = None, 10 ** 9
    while time.monotonic() < deadline:
        W = rng.permutation(np.repeat(np.arange(a), DEG))
        X = np.zeros(E, dtype=np.int64)
        for u in range(a):
            for v in range(a):
                ds = np.nonzero((U == u) & (W == v))[0]
                if len(ds):
                    X[ds] = rng.choice(N, len(ds), replace=False)
        cur = lift_cost(lift_nbr(a, N, MT, inv, U, W, X), V, sources)
        if cur < bestc:
            bestc, best = cur, (U.copy(), W.copy(), X.copy())
        if bestc == 0:
            return best, 0
        since = 0
        while since < patience and time.monotonic() < deadline:
            d = int(rng.integers(E))
            same = (U == U[d]) & (W == W[d])
            same[d] = False
            taken = set(X[same].tolist())
            x = int(rng.integers(N))
            if x in taken:
                since += 1
                continue
            old = int(X[d])
            X[d] = x
            c = lift_cost(lift_nbr(a, N, MT, inv, U, W, X), V, sources)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cur = c
                if cur < bestc:
                    bestc, best = cur, (U.copy(), W.copy(), X.copy())
                    since = 0
                    if bestc == 0:
                        return best, 0
                else:
                    since += 1
            else:
                X[d] = old
                since += 1
    return best, bestc


def lift_edges(a, N, MT, inv, U, W, X):
    nbr = lift_nbr(a, N, MT, inv, U, W, X)
    V = 2 * a * N
    edges = [(i, int(nbr[i, t])) for i in range(a * N) for t in range(DEG)]
    return V, edges


def lift_phase(deadline, rng):
    cands = []
    for a in (2, 3, 4):
        for N in range(1, 400):
            V = 2 * a * N
            if V < 685 or V > 700:
                continue
            for g in meta_groups(N, 3):
                cands.append((V, a, N) + g)
    cands.sort()
    if not cands:
        return None
    cache = {}
    i = 0
    slice_len = 3.0
    while time.monotonic() < deadline:
        V, a, N, m, k, lam = cands[i % len(cands)]
        key = (m, k, lam)
        if key not in cache:
            cache[key] = meta_table(m, k, lam)
        MT, inv = cache[key]
        end = min(deadline, time.monotonic() + slice_len)
        res, c = lift_search(a, N, MT, inv, end, rng)
        if res is not None and c == 0:
            U, W, X = res
            n, edges = lift_edges(a, N, MT, inv, U, W, X)
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
        i += 1
    return None


# ------------------------------------------------------------------------------ Haar near-miss search

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


HAAR_PLAN = [
    ('meta 117/3/16, 2 short', lambda: meta_table(117, 3, 16), [0, 184, 47, 48, 65, 21]),
    ('meta 71/5/5, 2 short', lambda: meta_table(71, 5, 5), [0, 92, 218, 269, 205, 88]),
]


def haar_phase(deadline, rng):
    for idx, (name, builder, S0) in enumerate(HAAR_PLAN):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(HAAR_PLAN) - idx)
        try:
            MT, inv = builder()
            S, c = search(MT, inv, DEG, S0, end, rng)
            if S is not None and c == 0:
                g = checked(MT, S, DEG, DIAM)
                if g is not None:
                    return g
        except Exception:
            continue
    return None


# --------------------------------------------------------------------------------------------- fallback

def trivial(d, D):
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def fallback_graph(d, D):
    try:
        MT, _ = meta_table(33, 10, 26)
        g = checked(MT, [0, 179, 116, 180, 47, 306], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ------------------------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = 0.8 * time_limit
    rng = np.random.default_rng(seed)
    try:
        g = lift_phase(t0 + 0.6 * budget, rng)
        if g is not None:
            return g
    except Exception:
        pass
    try:
        g = haar_phase(t0 + budget, rng)
        if g is not None:
            return g
    except Exception:
        pass
    return fallback_graph(d, D)
