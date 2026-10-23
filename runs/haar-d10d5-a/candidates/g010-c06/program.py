"""Haar-graph search for the bipartite degree-diameter problem, diameter 5 (numpy only).

A Haar graph of a group G and a d-set S has vertices A_g, B_g (g in G) and edges A_g ~ B_{s*g} (s in S).
It has diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  cost(S) counts the uncovered elements,
and cost 0 means the graph is valid.  Only graphs checked with lib.is_valid are returned.

New in this version:
  * propose(): replacement candidates mix uniform elements, products s_a*s_b and conjugates g*s*g^-1.
    Conjugates keep the word structure of a good set while moving it, which helps when uniform moves stall.
  * meta_candidates(): enumerates metacyclic groups Z_p x| Z_k (p prime, k | p-1) with order in a window,
    so the search tries several groups of order just above the record threshold (order > 2000 beats 4000).
  * elite restarts: restarts perturb the best set found so far, not only the start set.
  * exhaustive 1-swap scan of the best set whenever it reaches a low cost.
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


def _is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def meta_candidates(lo, hi, kmax=12):
    """Metacyclic groups Z_m x| Z_k with m prime, k | m-1, lo <= m*k <= hi, as (order, m, k, lam), sorted by order.
    lam = h^((m-1)/k) has order dividing k and is not 1, so lam^k = 1 mod m holds."""
    out = []
    for k in range(2, kmax + 1):
        for m in range(max(3, lo // k), hi // k + 2):
            if not (lo <= m * k <= hi) or (m - 1) % k or not _is_prime(m):
                continue
            for h in range(2, 60):
                lam = pow(h, (m - 1) // k, m)
                if lam != 1 and pow(lam, k, m) == 1:
                    out.append((m * k, m, k, lam))
                    break
    out.sort()
    return out


# ------------------------------------------------------------------------------------------------ search

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """(side-0 pair products S_i^-1 S_j, side-1 pair products S_i S_j^-1) as flat arrays."""
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid diameter-5 Haar graph)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by x, for every x in the int array X (only slot-i words are recomputed)."""
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
    """Score every single-slot replacement of S.  Returns (best cost, best S) or (large, None) if out of time."""
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


def propose(MT, inv, S, i, rng, K):
    """Candidate replacements for slot i: uniform elements, products s_a*s_b, conjugates g*s*g^-1."""
    N = MT.shape[0]
    rest = np.delete(S, i)
    t = K // 3
    parts = [rng.integers(0, N, size=K - 2 * t)]
    a = rng.choice(rest, t)
    b = rng.choice(rest, t)
    parts.append(MT[a, b])
    g = rng.integers(0, N, size=t)
    s = rng.choice(rest, t)
    parts.append(MT[MT[g, s], inv[g]])
    X = np.concatenate(parts).astype(np.int32)
    return np.unique(X[~np.isin(X, rest)])


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Anneal over d-subsets with elite restarts.  Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    scanned = set()
    S, cur, since = None, None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    if S0 is not None:
        S0 = np.array(S0, dtype=np.int32)
        c0 = cost(MT, inv, S0)
        best, bestc = S0.copy(), c0
        if c0 == 0:
            return best, 0
        c1, S1 = one_swap_scan(MT, inv, S0, time.monotonic() + 0.15 * (deadline - time.monotonic()))
        if S1 is not None and c1 < bestc:
            best, bestc = S1.copy(), c1
            if c1 == 0:
                return best, 0
        S = best.copy()
        cur = cost(MT, inv, S)

    while time.monotonic() < deadline:
        if S is None:
            if best is not None and rng.random() < 0.5:
                S = best.copy()
                for i in rng.choice(d, 2, replace=False):
                    S[i] = rng.integers(N)
                if len(set(S.tolist())) < d:
                    S = random_set()
            else:
                S = random_set()
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = S.copy(), cur
            if cur == 0:
                return best, 0

        i = int(rng.integers(d))
        X = propose(MT, inv, S, i, rng, K)
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
                if bestc <= 8 and bestc not in scanned:
                    scanned.add(bestc)
                    c2, S2 = one_swap_scan(MT, inv, best, min(deadline, time.monotonic() + 2.0))
                    if S2 is not None and c2 < bestc:
                        best, bestc = S2.copy(), c2
                        if c2 == 0:
                            return best, 0
                        S, cur = S2.copy(), c2
            elif delta < 0:
                since = 0
        since += 1
        if since > patience:
            S, cur = None, None
    return best, bestc


# --------------------------------------------------------------------------------------------- the graph

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
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def run(d, D, seed, time_limit, plan, fallback):
    """plan: list of (name, builder, S0 or None, weight); fallback: (builder, S) of a valid smaller graph."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.80 * time_limit
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

# Known near miss Z_401 x| Z_5 (order 2005, 6 short) with its start set, then order-window candidates.
PLAN = [
    ('meta 401/5/39, order 2005, 6 short', lambda: group_meta(401, 5, 39),
     [0, 399, 725, 919, 893, 646, 1508, 130, 652, 957], 5),
    ('meta 336/6/17, order 2016', lambda: group_meta(336, 6, 17), None, 1),
]

# Valid smaller Haar graph (order 1791, 3582 vertices), checked at run time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    plan = list(PLAN)
    for order, m, k, lam in meta_candidates(2001, 2100)[:4]:
        plan.append((f"meta {m}/{k}/{lam}, order {order}",
                     (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 0.5))
    return run(d, D, seed, time_limit, plan, FALLBACK)
