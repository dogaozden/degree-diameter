"""Haar-graph seed programs for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  Let G be a finite group and S a subset of G with |S| = d (the connection set).  The Haar graph has
vertices (g, A) and (g, B) for g in G and edges (g, A) ~ (s*g, B) for s in S.  It is bipartite and d-regular
with 2|G| vertices.  Right multiplication by any h in G is an automorphism, so every A-vertex looks like (e, A)
and every B-vertex like (e, B).  Its diameter is at most 5 iff
        (S^-1 S)^2 = G   and   (S S^-1)^2 = G.
COST(S) = number of group elements left uncovered; cost 0 = valid.

NEW IN THIS VERSION: a successive-halving group sweep.  Instead of spending a fixed slice on each group in a
fixed list, the program enumerates every metacyclic group Z_m x|_lam Z_k of order in [343, 372] (plus the known
non-abelian candidates), sorts them by order so that the smallest order that works is found first, and runs
annealing on all of them in rounds.  Each round doubles the per-group slice and keeps only the better half
(ranked by best cost so far), so the time goes to the groups that look closest to cost 0.  Every candidate
keeps its best set between rounds, so no work is thrown away.

WHAT THIS FILE DOES.  Builds group multiplication tables MT (MT[g, h] = g*h, element 0 = identity), then runs
a local search on S (K random replacements per step, incremental cost, Metropolis acceptance, restarts).
When cost reaches 0 the graph is built and CHECKED with lib.is_valid; only a checked graph is returned.
If nothing reaches cost 0, a precomputed valid smaller Haar graph is returned so the score is never 0.
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


def group_agl(q, k=None):
    """GF(q) x| C_k: maps t -> a*t + b on GF(q), a in the subgroup of order k of GF(q)^* (default AGL(1, q))."""
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


# ------------------------------------------------------------------------------------ group enumeration

def metacyclic_orders(lo, hi):
    """All (N, m, k, lam) with N = m*k in [lo, hi], lam != 1 (non-abelian), lam^k = 1 mod m, gcd(lam, m) = 1.
    One lam per (m, k) pair is kept, which is enough to give diverse groups."""
    out = []
    for N in range(lo, hi + 1):
        for m in range(3, N):
            if N % m:
                continue
            k = N // m
            if k < 2:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((N, m, k, lam))
                    break
    return out


def candidate_groups(lo=343, hi=372, limit=12):
    """Named builders for groups of order in [lo, hi], smallest order first, at most `limit` of them."""
    cands = [
        (343, 'Heis(7)', lambda: group_heis(7)),
        (351, 'Heis(3)xZ13', lambda: group_times_cyclic(group_heis(3), 13)),
        (360, 'AGL(1,9)xZ5', lambda: group_times_cyclic(group_agl(9), 5)),
        (360, 'AGL(1,5)xZ18', lambda: group_times_cyclic(group_agl(5), 18)),
    ]
    for N, m, k, lam in metacyclic_orders(lo, hi):
        cands.append((N, f'Z{m}x|Z{k}[{lam}]',
                      lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
    cands = [c for c in cands if lo <= c[0] <= hi]
    cands.sort(key=lambda c: c[0])
    return [(name, builder) for _, name, builder in cands[:limit]]


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
    """Score EVERY single-slot replacement of S.  Returns (best cost, best S)."""
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
    """Local search over d-subsets of the group.  With a start set S0: scan its 1-swap neighbours first, then
    anneal from it, restarting from a perturbed S0 (half the time) or a random set when stuck.
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


def run_sweep(d, D, seed, time_limit, cands, frac=0.80):
    """Successive-halving sweep over candidate groups.  Each round gives every surviving group a slice of
    time (the slice doubles each round), then keeps the better half by best cost so far.  Returns a checked
    (n, edges) as soon as some group reaches cost 0, or None."""
    t0 = time.monotonic()
    end_all = t0 + frac * time_limit
    rng = np.random.default_rng(seed)
    alive = [{'name': nm, 'builder': b, 'grp': None, 'S': None, 'c': 10 ** 9, 'dead': False}
             for nm, b in cands]
    if not alive:
        return None
    s = max(0.2, (end_all - t0) / (4.0 * len(alive)))
    while alive and time.monotonic() < end_all:
        for cand in alive:
            if time.monotonic() >= end_all:
                break
            if cand['grp'] is None:
                try:
                    cand['grp'] = cand['builder']()
                except Exception:
                    cand['dead'] = True
                    continue
            MT, inv = cand['grp']
            dl = min(end_all, time.monotonic() + s)
            try:
                S, c = search(MT, inv, d, cand['S'], dl, rng)
            except Exception:
                cand['dead'] = True
                continue
            if S is not None and c < cand['c']:
                cand['S'], cand['c'] = np.array(S, dtype=np.int32).copy(), c
            if cand['c'] == 0:
                g = checked(MT, cand['S'], d, D)
                if g is not None:
                    return g
        alive = [x for x in alive if not x['dead']]
        alive.sort(key=lambda x: x['c'])
        if len(alive) > 1:
            alive = alive[:max(1, (len(alive) + 1) // 2)]
        s *= 2
    return None


# ======================================================================================== cell: d6D5
TARGET = (6, 5)      # the (d, D) this plan is for; every other case gets a small always-valid graph

# Valid smaller Haar graph (order 330, 660 vertices), checked at run time; used only when the sweep fails.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        g = run_sweep(d, D, seed, time_limit, candidate_groups(343, 372, 12))
        if g is not None:
            return g
    except Exception:
        pass
    try:
        MT, _ = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
