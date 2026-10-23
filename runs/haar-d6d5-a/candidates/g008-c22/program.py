"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a set S of d elements, the Haar graph has vertices (g, A) and (g, B) for g in G,
and edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, and has 2|G| vertices.  Its diameter is at
most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered group elements, and cost 0 is valid.

VERSION NOTES.
  1. Product moves.  Half of the proposed replacements for a slot are products a*b or a^-1*b of two elements already
     in S (see `proposals`).
  2. Heisenberg group of order 343 = 7^3 is a candidate, just above the record half (342).
  3. Tiered best-so-far plan.  Candidates are checked by group order, and a candidate is skipped once it cannot beat
     the best valid graph already found.
  4. NEW: priority ordering.  The order-342 tier (ties the record, 684 vertices) runs FIRST, so the record is secured
     early.  The rest of the budget then goes to beat-the-record candidates (order > 342).  The safety tier
     (orders 331..341) runs last and is skipped automatically once a 684-vertex graph is in hand.  Previously the
     ascending sort spent budget on the safety tier before reaching the order-342 candidates.

Every returned graph is checked with lib.is_valid.  If nothing better is found, a precomputed valid Haar graph is
used, and a trivially valid graph is returned as the last resort.
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
    """GF(q) x| C_k: the maps t -> a*t + b with a in the subgroup of order k of GF(q)^* (default AGL(1, q))."""
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


def metacyclic_candidates(lo, hi, limit):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with lo <= m*k <= hi (one lam per (m, k)), smallest order first."""
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


# ------------------------------------------------------------------------------------------------ search

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j] (P an int array of pair products)."""
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


def one_swap_scan(MT, inv, S, deadline, chunk=512):
    """Score EVERY single-slot replacement of S (all slots x all group elements).  Returns (best cost, best S)."""
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


def proposals(MT, inv, S, i, rng, K):
    """Candidate replacements for slot i.  Half are products a*b or a^-1*b of two elements already in S
    (other slots), the rest are uniform random elements.  Elements already in S are removed."""
    N = MT.shape[0]
    rest = np.delete(S, i)
    npr = K // 2
    a = rest[rng.integers(0, len(rest), npr)]
    b = S[rng.integers(0, len(S), npr)]
    prod = np.where(rng.integers(0, 2, npr) == 0, MT[inv[a], b], MT[a, b])
    xr = rng.integers(0, N, K - npr)
    X = np.concatenate([prod, xr]).astype(np.int32)
    return X[~np.isin(X, rest)]


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Local search over d-subsets of the group.  With a start set S0: scan all its 1-swap neighbours first, then
    anneal from it, and restart from a perturbed S0 (half the time) or a random set when stuck.
    Returns (best S, best cost)."""
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
        c1, S1 = one_swap_scan(MT, inv, S0, time.monotonic() + 0.25 * max(0.0, deadline - time.monotonic()))
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
        X = proposals(MT, inv, S, i, rng, K)
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
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def run(d, D, seed, time_limit, plan, fallback):
    """plan: list of (name, order, builder, S0 or None, weight), in the order they should be tried.
    Keeps the largest checked valid graph found; a candidate is skipped if it cannot beat the current best."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.85 * time_limit
    rng = np.random.default_rng(seed)
    total_w = sum(e[4] for e in plan)
    best_g, best_n = None, 0
    for name, order, builder, S0, w in plan:
        now = time.monotonic()
        if now >= deadline_all:
            break
        if 2 * order <= best_n:
            total_w -= w
            continue
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, S0, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None and g[0] > best_n:
                best_g, best_n = g, g[0]
    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None and (best_g is None or g[0] > best_n):
            best_g = g
    except Exception:
        pass
    if best_g is not None:
        return best_g
    return trivial(d, D)


# ======================================================================================== cell: d6D5
TARGET = (6, 5)

# Near-miss seeds (element indices of the group table), from earlier searches.
NEAR = {(117, 3), (71, 5)}


def _plan():
    record_tier = []   # order 342: ties the record, tried first
    beat_tier = []     # order > 342: the only way to beat the record, gets most of the budget
    safety_tier = []   # orders 331..341: fallback improvements, skipped once 684 is found

    # Order 342 ties the record (684 vertices): affine group AGL(1,19) and metacyclic groups.
    record_tier.append(('AGL(1,19), order 342', 342, lambda: group_agl(19), None, 1.5))
    for m, k, lam in metacyclic_candidates(342, 342, 2):
        record_tier.append((f'meta {m}/{k}/{lam}, order 342', m * k,
                            (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 1.0))

    # Beat-the-record tier: order > 342.
    beat_tier.append(('Heisenberg mod 7, order 343', 343, lambda: group_heis(7), None, 2.0))
    for m, k, lam in metacyclic_candidates(343, 360, 8):
        if (m, k) in NEAR:
            continue
        beat_tier.append((f'meta {m}/{k}/{lam}, order {m * k}', m * k,
                          (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 1.0))
    # Near misses with seeds (2 short at 351 and 355, 4 short at 360).
    beat_tier.append(('meta 117/3/16, order 351, 2 short', 351,
                      lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21], 4.0))
    beat_tier.append(('meta 71/5/5, order 355, 2 short', 355,
                      lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88], 4.0))
    beat_tier.append(('SL(2,5) x Z_3, order 360, 4 short', 360,
                      lambda: group_times_cyclic(group_sl2(5), 3), [0, 246, 216, 211, 99, 132], 3.0))
    beat_tier.sort(key=lambda e: e[1])

    # Safety tier: orders 331..341 improve on the 660-vertex fallback.
    for m, k, lam in metacyclic_candidates(331, 341, 6):
        safety_tier.append((f'meta {m}/{k}/{lam}', m * k,
                            (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 0.5))
    safety_tier.sort(key=lambda e: e[1])

    return record_tier + beat_tier + safety_tier


PLAN = _plan()

# Valid smaller Haar graph (order 330, 660 vertices), used only if nothing better is found.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        return run(d, D, seed, time_limit, PLAN, FALLBACK)
    except Exception:
        return trivial(d, D)
