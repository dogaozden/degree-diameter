"""Haar-graph search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  For a finite group G and a connection set S (|S| = d), the Haar graph has vertices (g, A), (g, B)
and edges (g, A) ~ (s*g, B).  It is bipartite, d-regular, has 2|G| vertices, and has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G.  COST(S) counts the uncovered elements on both sides; cost 0 = valid.

NEW IN THIS VERSION.
  * Symmetry reduction: S -> hS leaves the cost unchanged, so we may assume the identity (element 0) is in S
    and never move slot 0.  Only d-1 slots are searched.
  * Tabu search over the FULL one-slot neighbourhood (every slot x every group element), with tenure on the
    removed element and aspiration on new global bests.  It replaces the annealing used before.
  * metacyclic_candidates(lo, hi) enumerates non-abelian groups Z_m x|_lam Z_k of every order in a range, so the
    plan is generated instead of hard-coded.  Groups of order >= 343 are needed to beat the 684-vertex record.

Every returned graph is checked with lib.is_valid.  If no group reaches cost 0, a checked smaller Haar graph is
returned, so the score is never 0 for a near miss.
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


def group_heis(p):
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
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


def metacyclic_candidates(lo, hi):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with lo <= m*k <= hi, one lam per (m, k).
    Returns sorted (order, m, k, lam) tuples."""
    out = []
    for m in range(2, hi + 1):
        for k in range(2, hi // m + 1):
            n = m * k
            if not lo <= n <= hi:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((n, m, k, lam))
                    break
    out.sort()
    return out


# ------------------------------------------------------------------------------------------------ cost

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


# ---------------------------------------------------------------------------------------- tabu search

def random_set(N, d, rng):
    """A random d-subset containing the identity (element 0), as int32."""
    return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)


def tabu_search(MT, inv, d, deadline, rng, stall=250):
    """Tabu search over d-subsets containing the identity.  Each step scores every one-slot replacement
    (slots 1..d-1, all group elements) and takes the best non-tabu move; the element removed is tabu for a
    short random tenure.  Restarts from a random set when stalled.  Returns (best S, best cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 9
    while time.monotonic() < deadline:
        S = random_set(N, d, rng)
        cur = cost(MT, inv, S)
        tabu = np.zeros((d, N), dtype=np.int64)
        it, since, run_best = 0, 0, cur
        while time.monotonic() < deadline:
            it += 1
            if cur < bestc:
                best, bestc = S.copy(), cur
            if cur == 0:
                return best, 0
            cc = np.full((d, N), np.inf)
            for i in range(1, d):
                rest = np.delete(S, i)
                X = np.setdiff1d(np.arange(N, dtype=np.int32), rest)
                cc[i, X] = batch_costs(MT, inv, S, i, X).astype(float)
                cc[i, S[i]] = np.inf          # staying put is not a move
            allowed = (tabu <= it) | (cc < bestc)
            score = np.where(allowed, cc, np.inf) + rng.random((d, N)) * 0.1
            flat = int(np.argmin(score))
            i, x = divmod(flat, N)
            if not np.isfinite(score[i, x]):
                break                          # every move is tabu: restart
            old = int(S[i])
            tabu[i, old] = it + int(rng.integers(4, 12))
            S[i] = x
            cur = int(cc[i, x])
            if cur < run_best:
                run_best, since = cur, 0
            else:
                since += 1
            if since > stall:
                break
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
    """plan: list of (group builder, seconds-weight); fallback: (builder, S) of a valid smaller graph."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    total_w = sum(w for _, w in plan)
    for builder, w in plan:
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = tabu_search(MT, inv, d, end, rng)
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


# ======================================================================================== cell: d6D5

TARGET = (6, 5)

FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def make_plan():
    """Groups of order >= 343 (record / 2 = 342), most promising first."""
    plan = []
    for n, m, k, lam in metacyclic_candidates(343, 370)[:6]:
        plan.append((lambda m=m, k=k, lam=lam: group_meta(m, k, lam), 1.0))
    plan.insert(0, (lambda: group_heis(7), 1.0))                       # order 343
    plan.append((lambda: group_times_cyclic(group_heis(3), 13), 1.0))  # order 351
    plan.append((lambda: group_times_cyclic(group_agl(9), 5), 1.0))    # order 360
    return plan


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run(d, D, seed, time_limit, make_plan(), FALLBACK)
