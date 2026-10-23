"""Bold variant for d=10, D=5: bipartite voltage lifts over non-abelian groups, with Haar search as fallback.

Base graph: two A-fibres and two B-fibres. Each A-fibre joins each B-fibre through a set of group darts,
so every vertex has degree 10 and the graph has 4N vertices. The lift is invariant under right
multiplication by G, so the diameter is at most 5 iff a BFS from each of the four fibre identities
reaches all 4N vertices within 5 steps. Annealing over the dart sets minimises the number of unreached
vertices. Any valid lift with N >= 1001 gives at least 4004 vertices, which beats the record of 4000.

If no lift is found, the Haar search from the parent program runs in the remaining time, and a
precomputed valid Haar graph is the last resort. Every returned graph is checked with lib.is_valid.
"""
import math
import time

import numpy as np

import lib


TARGET = (10, 5)
DEG = 10
D_TARGET = 5

# Lift search (bold family)
LIFT_LO, LIFT_HI = 1001, 1100
SLICE_L = 5.0
C_OPTS = [((5, 5), (5, 5)), ((6, 4), (4, 6)), ((4, 6), (6, 4))]

# Haar search (parent family, kept as fallback)
LO, HI = 1792, 2100
SLICE_H = 4.0
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j. Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + \
                    (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def metacyclic_candidates(lo, hi):
    """(N, m, k, lam) with N = m*k in [lo, hi], k >= 2, m >= 3, lam a non-trivial unit with lam^k = 1 mod m."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1:
                    continue
                out.append((N, m, k, lam))
    return out


# ------------------------------------------------------------------- bold: voltage lift search

def lift_nbr(MT, inv, N, darts):
    """Neighbour array (4N x DEG). A-fibre i is ids i*N..; B-fibre j is ids 2N+j*N..; dart (i, j, g) joins
    (i, x) to (j, g*x)."""
    n = 4 * N
    nbr = np.empty((n, DEG), dtype=np.int64)
    colA = [0, 0]
    colB = [0, 0]
    for i, j, g in darts:
        nbr[i * N:(i + 1) * N, colA[i]] = 2 * N + j * N + MT[g].astype(np.int64)
        colA[i] += 1
        nbr[2 * N + j * N:2 * N + (j + 1) * N, colB[j]] = i * N + MT[int(inv[g])].astype(np.int64)
        colB[j] += 1
    return nbr


def lift_cost(MT, inv, N, darts):
    """Number of (fibre identity, vertex) pairs at distance > D_TARGET. Zero means diameter <= 5."""
    nbr = lift_nbr(MT, inv, N, darts)
    n = 4 * N
    cost = 0
    for src in (0, N, 2 * N, 3 * N):
        vis = np.zeros(n, dtype=bool)
        vis[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(D_TARGET):
            cand = nbr[fr].ravel()
            cand = cand[~vis[cand]]
            if cand.size == 0:
                break
            cand = np.unique(cand)
            vis[cand] = True
            fr = cand
        cost += n - int(vis.sum())
    return cost


def lift_anneal(MT, inv, N, C, rng, deadline, K=4, T=0.8, patience=1500):
    """Anneal dart sets for base counts C. Returns the dart list when cost reaches 0, else None."""
    pairs = [(i, j, C[i][j]) for i in range(2) for j in range(2) if C[i][j] > 0]

    def rand_state():
        return [rng.choice(N, c, replace=False).astype(np.int64) for _, _, c in pairs]

    def darts_of(S):
        return [(pairs[p][0], pairs[p][1], int(g)) for p in range(len(pairs)) for g in S[p]]

    S = rand_state()
    cur = lift_cost(MT, inv, N, darts_of(S))
    best, since = cur, 0
    while cur > 0 and time.monotonic() < deadline:
        p = int(rng.integers(len(pairs)))
        s = int(rng.integers(pairs[p][2]))
        bc, bS = None, None
        for _ in range(K):
            x = int(rng.integers(N))
            if x in S[p]:
                continue
            trial = [arr.copy() for arr in S]
            trial[p][s] = x
            c = lift_cost(MT, inv, N, darts_of(trial))
            if bc is None or c < bc or (c == bc and rng.random() < 0.5):
                bc, bS = c, trial
        if bS is None:
            continue
        delta = bc - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S, cur = bS, bc
            if cur < best:
                best, since = cur, 0
        since += 1
        if since > patience:
            S = rand_state()
            cur = lift_cost(MT, inv, N, darts_of(S))
            best, since = cur, 0
    if cur == 0:
        return darts_of(S)
    return None


def run_lift(rng, deadline):
    """Sweep non-abelian metacyclic groups of order in [LIFT_LO, LIFT_HI] in ascending order. Keep the largest
    lift that passes lib.is_valid. Returns (n, edges) or None."""
    groups = {}
    for c in metacyclic_candidates(LIFT_LO, LIFT_HI):
        groups.setdefault(c[0], []).append(c)
    order = []
    for N in sorted(groups):
        grp = groups[N]
        rng.shuffle(grp)
        order.extend(grp)

    best, best_n = None, 0
    for N, m, k, lam in order:
        now = time.monotonic()
        if deadline - now < 1.0:
            break
        if 4 * N <= best_n:
            continue
        try:
            MT, inv = group_meta(m, k, lam)
            C = C_OPTS[int(rng.integers(len(C_OPTS)))]
            darts = lift_anneal(MT, inv, N, C, rng, min(deadline, now + SLICE_L))
            if darts is None:
                continue
            nbr = lift_nbr(MT, inv, N, darts)
            n = 4 * N
            edges = [(a, b) for a in range(2 * N) for b in nbr[a].tolist()]
            if lib.is_valid(n, edges, DEG, D_TARGET):
                best, best_n = (n, edges), n
        except Exception:
            continue
    return best


# ------------------------------------------------------------------ parent: Haar search fallback

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
    """Annealing over d-subsets of the group, random restarts when stuck. Returns (best S, best cost)."""
    N = MT.shape[0]

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0
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


def run_haar(d, D, rng, deadline):
    keyed = {}
    for c in metacyclic_candidates(LO, HI):
        keyed.setdefault(c[0], []).append(c)
    order = []
    for N in sorted(keyed):
        grp = keyed[N]
        rng.shuffle(grp)
        order.extend(grp)
    if not order:
        return None
    idx = 0
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.5:
            break
        _, m, k, lam = order[idx % len(order)]
        idx += 1
        try:
            MT, inv = group_meta(m, k, lam)
            S, c = search(MT, inv, d, min(deadline, now + SLICE_H), rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g
    return None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    rng = np.random.default_rng(seed)

    res = run_lift(rng, t0 + 0.6 * time_limit)
    if res is not None:
        return res

    g = run_haar(d, D, rng, t0 + 0.88 * time_limit)
    if g is not None:
        return g

    try:
        MT, inv = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
