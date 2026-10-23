"""Bipartite degree-diameter search for (d, D) = (10, 5).

Two constructions are tried in order:
  1. Voltage lifts over metacyclic groups N = Z_m x| Z_k with a base graph of
     a + a vertices (a = 2 or 3) and random multiplicities. Left multiplication by a group
     element is an automorphism, so each part is one orbit and it suffices to check the
     eccentricities of one representative per part (cost 0 = valid). Orders 2*a*|G| above
     4000 are sought, which needs |G| >= 1001.
  2. Fallback: the Haar-graph annealing from the parent program (order 2|G| with |G| >= 1792).

Every returned graph is verified with lib.is_valid. Other (d, D) cases get a small valid graph.
"""
import math
import time

import numpy as np

import lib


TARGET = (10, 5)
LIFT_LO, LIFT_HI = 1001, 1080     # group orders for the voltage-lift phase (4 * 1001 = 4004 > 4000)
LIFT_SLICE = 2.0                  # seconds per candidate group in the lift phase
HAAR_LO, HAAR_HI = 1792, 2100     # group orders for the Haar fallback
HAAR_SLICE = 4.0


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
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


def metacyclic_candidates(lo, hi):
    """All (N, m, k, lam) with N = m*k in [lo, hi], k >= 2, m >= 3, lam a nontrivial unit with lam^k = 1 mod m."""
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


# ----------------------------------------------------------- voltage lifts (new construction)

def random_multiplicity(a, d, rng):
    """a x a nonnegative integer matrix with all row and column sums d (sum of d random permutations)."""
    M = np.zeros((a, a), dtype=np.int64)
    for _ in range(d):
        M[np.arange(a), rng.permutation(a)] += 1
    return M


def lift_nbr(MT, a, darts, d):
    """Neighbour array (V, d) of the lift. Parts: A_i = i*N + x, B_j = (a+j)*N + x.
    Dart (i, j, g) joins (x, A_i) to (x*g, B_j) for every x. Returns None if not d-regular."""
    N = MT.shape[0]
    V = 2 * a * N
    xs = np.arange(N, dtype=np.int64)
    As, Bs = [], []
    for i, j, g in darts:
        As.append(i * N + xs)
        Bs.append((a + j) * N + MT[xs, g].astype(np.int64))
    A = np.concatenate(As)
    B = np.concatenate(Bs)
    src = np.concatenate([A, B])
    dst = np.concatenate([B, A])
    if not np.array_equal(np.bincount(src, minlength=V), np.full(V, d, dtype=np.int64)):
        return None
    order = np.argsort(src, kind="stable")
    return dst[order].reshape(V, d)


def lift_cost(nbr, reps, D):
    """Uncovered (vertex, representative) pairs after D rounds of BFS from each representative."""
    V = nbr.shape[0]
    total = 0
    for r in reps:
        reach = np.zeros(V, dtype=bool)
        reach[r] = True
        for _ in range(D):
            reach = reach | reach[nbr].any(axis=1)
        total += V - int(reach.sum())
    return total


def anneal_lift(MT, a, d, D, deadline, rng):
    """Random restarts plus annealing over the voltages of a fixed multiplicity matrix.
    Returns (darts, nbr) with lift cost 0, or None."""
    N = MT.shape[0]
    reps = [i * N for i in range(a)] + [(a + j) * N for j in range(a)]
    while time.monotonic() < deadline:
        M = random_multiplicity(a, d, rng)
        darts, used = [], {}
        for i in range(a):
            for j in range(a):
                m = int(M[i, j])
                if m == 0:
                    continue
                gs = [int(g) for g in rng.choice(N, size=m, replace=False)]
                used[(i, j)] = set(gs)
                darts += [(i, j, g) for g in gs]
        nbr = lift_nbr(MT, a, darts, d)
        if nbr is None:
            continue
        c = lift_cost(nbr, reps, D)
        T = 1.0
        while c > 0 and time.monotonic() < deadline:
            k = int(rng.integers(len(darts)))
            i, j, g = darts[k]
            g2 = int(rng.integers(N))
            if g2 in used[(i, j)]:
                continue
            nd = list(darts)
            nd[k] = (i, j, g2)
            nn = lift_nbr(MT, a, nd, d)
            if nn is None:
                continue
            c2 = lift_cost(nn, reps, D)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                darts, nbr, c = nd, nn, c2
                used[(i, j)].discard(g)
                used[(i, j)].add(g2)
            T = max(0.05, T * 0.998)
        if c == 0:
            return darts, nbr
    return None


def lift_phase(d, D, deadline, rng):
    """Search metacyclic groups of order in [LIFT_LO, LIFT_HI] for a valid voltage lift. Returns (n, edges) or None."""
    cands = metacyclic_candidates(LIFT_LO, LIFT_HI)
    rng.shuffle(cands)
    for (N, m, k, lam) in cands:
        if time.monotonic() >= deadline:
            break
        try:
            MT, _ = group_meta(m, k, lam)
        except Exception:
            continue
        a = 2 if rng.random() < 0.5 else 3
        slice_end = min(deadline, time.monotonic() + LIFT_SLICE)
        res = anneal_lift(MT, a, d, D, slice_end, rng)
        if res is None:
            continue
        _, nbr = res
        V = nbr.shape[0]
        u = np.repeat(np.arange(V, dtype=np.int64), d)
        v = nbr.ravel()
        keep = u < v
        edges = list(zip(u[keep].tolist(), v[keep].tolist()))
        if lib.is_valid(V, edges, d, D):
            return V, edges
    return None


# ------------------------------------------------------------ Haar-graph fallback (parent)

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
    """Cost of S with slot i replaced by each x in X."""
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
    """Annealing over d-subsets of the group containing the identity. Returns (best S, best cost)."""
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
        since += 1
        if since > patience:
            S = None
    return best, bestc


def haar_edges(MT, S):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def run_meta(d, D, seed, time_limit):
    """Round-robin Haar annealing over metacyclic groups of order in [HAAR_LO, HAAR_HI]."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.88 * time_limit
    rng = np.random.default_rng(seed)

    keyed = {}
    for c in metacyclic_candidates(HAAR_LO, HAAR_HI):
        keyed.setdefault(c[0], []).append(c)
    order = []
    for N in sorted(keyed):
        grp = keyed[N]
        rng.shuffle(grp)
        order.extend(grp)

    idx = 0
    while order:
        now = time.monotonic()
        remaining = deadline_all - now
        if remaining < 0.5:
            break
        _, m, k, lam = order[idx % len(order)]
        idx += 1
        slice_end = now + min(HAAR_SLICE, remaining)
        try:
            MT, inv = group_meta(m, k, lam)
            S, c = search(MT, inv, d, slice_end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g
    return trivial(d, D)


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    rng = np.random.default_rng(seed)
    try:
        res = lift_phase(d, D, t0 + 0.5 * time_limit, rng)
        if res is not None:
            return res
    except Exception:
        pass
    elapsed = time.monotonic() - t0
    rem = max(1.0, 0.8 * time_limit - elapsed)
    try:
        return run_meta(d, D, seed, rem / 0.88)
    except Exception:
        return trivial(d, D)
