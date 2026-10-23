"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a set S of d elements, the Haar graph has vertices A_g and B_g (g in G)
and edges A_g ~ B_{s g} for s in S.  It is bipartite, d-regular, has 2|G| vertices, and is diameter <= 5
iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements of both conditions; cost 0 is valid.

NEW IN THIS VERSION.
  * greedy_start: builds a connection set by repeatedly adding the element that covers the most words
    (randomised tie-break), giving starts that are far better than random sets.
  * conjugate moves: a third of the candidate replacements are conjugates g*s*g^-1 of existing elements.
    Conjugation keeps the group-theoretic structure of S while changing its cover pattern.
  * a multi-candidate run that keeps the LARGEST checked valid graph, so a later group can beat an
    earlier one, and groups of order 331..342 are tried as cheap fallbacks below the record.

Every returned graph is checked with lib.is_valid.  A small always-valid graph is the last resort.
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
    """Table of a group given as an (N, c) integer coordinate array (element 0 = identity) and a vectorised product."""
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


def metacyclic_candidates(lo, hi, limit):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with lo <= m*k <= hi, smallest order first."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or lam % m == 1:
                    continue
                if pow(lam, k, m) == 1 % m:
                    out.append((m, k, lam))
                    break
        if len(out) >= limit:
            break
    return out[:limit]


# ------------------------------------------------------------------------------------------ cost machinery

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """(side-0 products S_i^-1 S_j, side-1 products S_i S_j^-1) as flat arrays."""
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (0 = valid).  Monotone in S, so it also scores partial sets."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """cost of S with slot i replaced by x, for every x in the int array X (only slot-i words are recomputed)."""
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


# ------------------------------------------------------------------------------- NEW: construction helpers

def random_set(N, d, rng):
    """A random d-subset containing the identity (cost is invariant under left translation, so this loses nothing)."""
    return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)


def greedy_start(MT, inv, d, rng, deadline):
    """NEW: grow S one element at a time, each time adding the element that minimises the cost of the partial set
    (random tie-break).  Returns a d-set, or None if the deadline passes first."""
    N = MT.shape[0]
    S = [0]
    while len(S) < d:
        if time.monotonic() >= deadline:
            return None
        cand = np.array([x for x in range(1, N) if x not in S], dtype=np.int32)
        cs = np.array([cost(MT, inv, np.array(S + [int(x)], dtype=np.int32)) for x in cand])
        j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
        S.append(int(cand[j]))
    return np.array(S, dtype=np.int32)


def propose(MT, inv, S, i, rng, K):
    """NEW: candidate replacements for slot i: two thirds uniform random, one third conjugates g*s*g^-1 of
    current elements s, which keep the group-theoretic shape of S while moving its cover pattern."""
    N = MT.shape[0]
    rest = np.delete(S, i)
    nc = K // 3
    X = rng.integers(0, N, size=K).astype(np.int32)
    g = rng.integers(0, N, size=nc)
    base = rest[rng.integers(0, len(rest), size=nc)]
    X[:nc] = MT[MT[g, base], inv[g]]
    return X[~np.isin(X, rest)]


def perturb(S0, d, N, rng):
    """Two random slot changes of S0, or a random set if they collide."""
    S = np.array(S0, dtype=np.int32).copy()
    for i in rng.choice(d, 2, replace=False):
        S[i] = rng.integers(N)
    if len(set(S.tolist())) < d:
        return random_set(N, d, rng)
    return S


def search(MT, inv, d, S0, deadline, rng, K=32, temp=0.45, patience=3000):
    """Simulated annealing over d-subsets with the new starts and conjugate moves.
    Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S = None if S0 is None else np.array(S0, dtype=np.int32)
    if S is not None:
        c0 = cost(MT, inv, S)
        best, bestc = S.copy(), c0
        if c0 == 0:
            return best, 0
    cur, since = None, 0
    while time.monotonic() < deadline:
        if S is None:
            r = rng.random()
            if S0 is not None and r < 0.4:
                S = perturb(S0, d, N, rng)
            elif r < 0.75:
                S = greedy_start(MT, inv, d, rng, deadline)
                if S is None:
                    break
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
    if d >= 2 and D >= 2:
        n = 2 * D                       # even cycle C_{2D}: bipartite, degree 2, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if d >= 1 and D >= 1:
        return 2, [(0, 1)]
    return 1, []


def run(d, D, seed, time_limit, plan, fallback):
    """Run every plan entry within the budget and keep the LARGEST checked valid graph."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.8 * time_limit
    rng = np.random.default_rng(seed)
    total_w = sum(w for *_, w in plan)
    best = None
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
            if g is not None and (best is None or g[0] > best[0]):
                best = g
    if best is not None:
        return best
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

# Near misses: 351 and 355 are 2 short, 360 is 4 short; annealing starts from them.
PLAN = [
    ('meta 117/3/16, order 351', lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21], 6),
    ('meta 71/5/5, order 355', lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88], 6),
    ('SL(2,5) x Z_3, order 360', lambda: group_times_cyclic(group_sl2(5), 3), [0, 246, 216, 211, 99, 132], 4),
]

# Random-start greedy searches over metacyclic groups just above the record half (343..360).
EXTRA = [
    (f'meta {m}/{k}/{lam}, order {m * k}', (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 1)
    for (m, k, lam) in metacyclic_candidates(343, 360, 8)
]

# Cheaper fallbacks at or just below the record half (331..342 gives n = 662..684).
LOWER = [
    (f'meta {m}/{k}/{lam}, order {m * k}', (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 1)
    for (m, k, lam) in metacyclic_candidates(331, 342, 4)
]

# Known valid smaller Haar graph (order 330, n = 660), used only if nothing better checks out.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        return run(d, D, seed, time_limit, PLAN + EXTRA + LOWER, FALLBACK)
    except Exception:
        return trivial(d, D)
