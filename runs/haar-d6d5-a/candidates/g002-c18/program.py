"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a connection set S (|S| = d), the Haar graph has vertices (g, A), (g, B)
and edges (g, A) ~ (s*g, B) for s in S.  It is bipartite, d-regular, with 2|G| vertices.  Its diameter is at
most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  cost(S) counts the uncovered group elements on both sides;
cost 0 means valid.

WHAT IS NEW HERE.
  * guided_candidates: a targeted move.  Pick an element x that the current S fails to cover, then build a
    new slot value that creates a word w with x = w*f for some existing word f.  This replaces most purely
    random proposals, so the search moves toward uncovered elements instead of sampling blindly.
  * metacyclic_plan: enumerates non-abelian metacyclic groups Z_m x| Z_k of each order in a range, choosing,
    for each order, the action lam with the largest multiplicative order.  These groups become the search
    targets just above the threshold 342 (group order > 342 gives 2|G| > 684 vertices).

Every returned graph is checked with lib.is_valid.  If no search reaches cost 0, a valid smaller Haar graph
is returned instead.
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
    """Table of a group given as an (N, c) coordinate array (element 0 = identity) and a vectorised product."""
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
    """Heisenberg group mod p (upper unitriangular 3x3), order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

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


# ------------------------------------------------------------------------------ NEW: group enumeration

def _mult_order(lam, m):
    """Multiplicative order of lam modulo m (lam coprime to m)."""
    x, o = lam % m, 1
    while x != 1 % m:
        x = x * lam % m
        o += 1
    return o


def metacyclic_plan(lo, hi, count):
    """For each order N in [lo, hi], find the non-abelian metacyclic group Z_m x| Z_k (m*k = N, m >= 3, k >= 2)
    whose action lam has the largest multiplicative order (strongest non-commutativity).  Returns up to
    `count` tuples (N, m, k, lam), in increasing N."""
    picks = []
    for order in range(lo, hi + 1):
        best = None
        for k in range(2, order // 3 + 1):
            if order % k:
                continue
            m = order // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1:
                    continue
                o = _mult_order(lam, m)
                if best is None or (o, m) > (best[0], best[1]):
                    best = (o, m, k, lam)
        if best is not None:
            picks.append((order, best[1], best[2], best[3]))
            if len(picks) >= count:
                break
    return picks


# ------------------------------------------------------------------------------------------ cost

def _cover(MT, N, P):
    """Boolean array of the elements covered by the products P[i]*P[j]."""
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    """(side-0 pair products s_i^-1 s_j, side-1 pair products s_i s_j^-1) as flat arrays."""
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    """Uncovered elements, both sides (cost 0 = valid)."""
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    """Cost of S with slot i replaced by each x in X (only the words involving slot i are recomputed)."""
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


# ------------------------------------------------------------------ NEW: coverage-guided proposals

def guided_candidates(MT, inv, S, i, rng, K):
    """Proposals for slot i aimed at uncovered elements.  Pick an uncovered x on a random side, an existing
    word f on that side, and an existing slot value s_j.  Then set the slot so that a new word w satisfies
    x = w*f (side 0: s_i = s_j f x^-1; side 1: s_i = x f^-1 s_j).  A few random values are mixed in.
    Correctness does not depend on this: every candidate is still scored exactly by batch_costs."""
    N = MT.shape[0]
    rest = np.delete(S, i)
    P0, P1 = _pairs(MT, inv, S)
    sides = []
    for P in (P0, P1):
        F = np.unique(P)
        sides.append((F, np.flatnonzero(~_cover(MT, N, F))))
    out = np.empty(K, dtype=np.int32)
    for t in range(K):
        side = int(rng.integers(2))
        F, unc = sides[side]
        if len(unc) == 0 or rng.random() < 0.15:
            out[t] = rng.integers(N)
            continue
        x = int(unc[rng.integers(len(unc))])
        f = int(F[rng.integers(len(F))])
        sj = int(rest[rng.integers(len(rest))])
        if side == 0:
            out[t] = MT[MT[sj, f], inv[x]]
        else:
            out[t] = MT[MT[x, inv[f]], sj]
    return out


def search(MT, inv, d, deadline, rng, K=24, temp=0.45, patience=4000):
    """Anneal over d-subsets with guided and random proposals, restarting from a random set when stuck.
    Returns (best S, best cost); cost 0 means valid."""
    N = MT.shape[0]

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    best, bestc = None, 10 ** 9
    S, cur, since = None, None, 0
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
        if rng.random() < 0.7:
            X = guided_candidates(MT, inv, S, i, rng, K)
        else:
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


# --------------------------------------------------------------------------------------------- graph

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if lib.is_valid rejects it."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def run(d, D, seed, time_limit, plan, fallback):
    """plan: list of (name, builder, weight); fallback: (builder, S) of a valid smaller Haar graph."""
    t0 = time.monotonic()
    deadline_all = t0 + min(0.75 * time_limit, time_limit - 8.0)
    rng = np.random.default_rng(seed)
    total_w = sum(w for _, _, w in plan)
    for name, builder, w in plan:
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, end, rng)
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


# ================================================================================== target d6D5

TARGET = (6, 5)


def make_plan():
    """Groups of order just above 342, with the metacyclic groups chosen by metacyclic_plan."""
    plan = [
        ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13), 2),
        ('Heis(7), order 343', lambda: group_heis(7), 2),
        ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5), 2),
    ]
    for order, m, k, lam in metacyclic_plan(344, 400, 3):
        plan.append((f'Z{m} x| Z{k} lam={lam}, order {order}',
                     (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), 2))
    return plan


# Valid smaller Haar graph (order 330, 660 vertices), checked at run time.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run(d, D, seed, time_limit, make_plan(), FALLBACK)
