"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy + lib only).

THEORY.  For a finite group G and a connection set S (|S| = d), the Haar graph has vertices (g, A), (g, B) and
edges (g, A) ~ (s*g, B).  It is bipartite, d-regular, has 2|G| vertices, and its diameter is at most 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered group elements, and cost 0 means valid.
Left-translating S (S -> tS) leaves the cost unchanged, so we may assume 0 is in S.

NEW IN THIS VERSION.
  * greedy_set: a randomized greedy cover builder.  It grows S one element at a time, picking among the
    best-scoring candidates by how many elements the partial pair-products cover.  The annealer restarts
    from these sets (80% of restarts) instead of uniform random sets.
  * metacyclic_candidates: enumerates non-abelian metacyclic groups Z_m x| Z_k of orders in a given range,
    so the plan can try many more groups near the threshold |G| = 343 (2|G| = 686 > record 684).

Every returned graph is checked with lib.is_valid.  A valid smaller Haar graph is the fallback.
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


def metacyclic_candidates(lo, hi, limit):
    """NEW HELPER.  Non-abelian metacyclic groups Z_m x| Z_k of order N = m*k in [lo, hi].
    For each order N, prefer the largest k that admits a nontrivial lam with lam^k = 1 mod m, gcd(lam, m) = 1.
    Returns up to `limit` tuples (N, m, k, lam), sorted by order."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(N - 1, 1, -1):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lam = next((l for l in range(2, m) if math.gcd(l, m) == 1 and pow(l, k, m) == 1), None)
            if lam is not None:
                out.append((N, m, k, lam))
                break
        if len(out) >= limit:
            break
    return out


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
    """GF(q) x| C_k: maps t -> a*t + b with a in the order-k subgroup of GF(q)^* (default AGL(1, q))."""
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
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k
                                 + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


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


def cover_score(MT, inv, T):
    """Number of covered elements (both sides) for a partial set T.  Larger is better."""
    N = MT.shape[0]
    P0, P1 = _pairs(MT, inv, T)
    return int(_cover(MT, N, np.unique(P0)).sum()) + int(_cover(MT, N, np.unique(P1)).sum())


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


def random_set(N, d, rng):
    """A uniform random d-subset of the group that contains the identity (WLOG, by left translation)."""
    return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)


def greedy_set(MT, inv, d, rng, pool=6):
    """NEW HELPER.  Randomized greedy cover: start from {0} and repeatedly add the element that covers the
    most group elements by the partial pair-products.  Ties and near-ties are broken at random by choosing
    among the `pool` best candidates, so repeated calls give diverse starts."""
    N = MT.shape[0]
    S = [0]
    while len(S) < d:
        cands = np.array([x for x in range(1, N) if x not in S], dtype=np.int64)
        sc = np.array([cover_score(MT, inv, np.array(S + [int(x)], dtype=np.int32)) for x in cands],
                      dtype=float)
        sc += rng.random(len(cands)) * 2.0
        top = np.argsort(-sc)[:pool]
        S.append(int(cands[top[int(rng.integers(len(top)))]]))
    return np.array(S, dtype=np.int32)


def make_setter(MT, inv, d, p_greedy=0.8, pool=6):
    """Start-set generator for restarts: greedy most of the time, uniform random otherwise."""
    N = MT.shape[0]

    def make(rng):
        if rng.random() < p_greedy:
            return greedy_set(MT, inv, d, rng, pool)
        return random_set(N, d, rng)
    return make


def search(MT, inv, d, deadline, rng, make_set, K=24, temp=0.45, patience=3000):
    """Simulated annealing over d-subsets.  Each step scores K random replacements of one slot at once.
    On stagnation, restart from make_set(rng).  Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0
    while time.monotonic() < deadline:
        if S is None:
            S = np.array(make_set(rng), dtype=np.int32)
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
                best, bestc = S.copy(), cur
                since = 0
                if cur == 0:
                    return best, 0
            elif delta < 0:
                since = 0
        since += 1
        if since > patience:
            S = None
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
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    n, edges = lib.haar_graph(d, range(d))
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return 2, [(0, 1)]


def run(d, D, seed, time_limit, plan, fallback):
    """plan: list of (name, builder, weight); fallback: (builder, S) of a valid smaller Haar graph."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.78 * time_limit
    rng = np.random.default_rng(seed)
    total_w = float(sum(w for _, _, w in plan))
    for name, builder, w in plan:
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, end, rng, make_setter(MT, inv, d))
        except Exception:
            continue
        if S is not None and c == 0:
            try:
                g = checked(MT, S, d, D)
            except Exception:
                g = None
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


# ======================================================================================== cell: d6D5
TARGET = (6, 5)


def make_plan():
    """Static groups of order near the threshold 343, then metacyclic groups of orders 343..372."""
    plan = [
        ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13), 2),
        ('Heis(7), order 343', lambda: group_heis(7), 2),
        ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5), 2),
    ]
    for N, m, k, lam in metacyclic_candidates(343, 372, 4):
        plan.append((f'Z_{m} x| Z_{k} (lam={lam}), order {N}',
                     lambda m=m, k=k, lam=lam: group_meta(m, k, lam), 1))
    return plan


# Valid smaller Haar graph, checked at run time; used only when no plan entry reaches cost 0.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        return run(d, D, seed, time_limit, make_plan(), FALLBACK)
    except Exception:
        return trivial(d, D)
