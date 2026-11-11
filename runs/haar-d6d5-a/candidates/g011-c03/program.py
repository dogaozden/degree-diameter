"""Haar-graph seed programs for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  Let G be a finite group and S a subset of G with |S| = d (the connection set).  The Haar graph has
vertices (g, A) and (g, B) for g in G and edges (g, A) ~ (s*g, B) for s in S.  It is bipartite and d-regular
with 2|G| vertices.  Right multiplication by any h in G is an automorphism, so every A-vertex looks like (e, A)
and every B-vertex like (e, B).  Its diameter is at most 5 iff
        (S^-1 S)^2 = G   and   (S S^-1)^2 = G
(the left set covers the A side, the right set the B side).  COST(S) = number of group elements left uncovered;
cost 0 = valid.

WHAT THIS FILE DOES.  Builds the group as a multiplication table MT and runs a local search on S.  NEW IN THIS
VERSION: targeted moves.  Given an uncovered element u on either side, a slot x is proposed so that some word
involving x equals u*q^-1 for a pair product q, which makes u covered.  Half of each batch of candidates are such
targeted moves, the other half are uniformly random.  Successive halving over candidate groups allocates time,
and only a checked graph (lib.is_valid) is ever returned; a smaller valid Haar graph is the fallback.
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
    """GF(q) x| C_k: the maps t -> a*t + b on GF(q) with a in the subgroup of order k of GF(q)^* (default k = q-1,
    that is AGL(1, q)).  q a prime power (uses lib.GF).  The product is (b1, a1)(b2, a2) = (b1 + a1*b2, a1*a2)."""
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
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with lo <= m*k <= hi, one per (m, k), smallest order first."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((f"Z_{m} x| Z_{k} (lam={lam}), order {N}", N, m, k, lam))
                    break
            if len(out) >= limit:
                return out
    return out


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
            Q = np.concatenate([MT[xi[:, None], rest[None, :]], MT[ri[None, :], X[:, None]]], axis=1)   # x^-1 s, s^-1 x
        else:
            Q = np.concatenate([MT[X[:, None], ri[None, :]], MT[rest[None, :], xi[:, None]]], axis=1)   # x s^-1, s x^-1
        W = np.concatenate([MT[Q[:, :, None], F[None, None, :]].reshape(K, -1),
                            MT[F[None, None, :], Q[:, :, None]].reshape(K, -1),
                            MT[Q[:, :, None], Q[:, None, :]].reshape(K, -1)], axis=1)
        new = ~base[W]
        flat = (W + offs)[new]
        cnt = np.bincount(flat, minlength=K * N).reshape(K, N)
        total += N - int(base.sum()) - (cnt > 0).sum(axis=1)
    return total


def targeted(MT, inv, S, i, rng, count):
    """NEW MOVE: propose values for slot i that cover a currently uncovered element.

    Pick an uncovered element u on side 0 or side 1 and a random pair product q of that side.  Then
      side 0: x = s q u^-1   (so x^-1 s = u q^-1, and (x^-1 s) q = u),
      side 1: x = u q^-1 s   or   x = q u^-1 s   (so x s^-1 = u q^-1, or s x^-1 = u q^-1),
    with s a random other element of S.  Returns an int32 array of up to `count` candidates.
    """
    N = MT.shape[0]
    rest = np.delete(S, i)
    Si = inv[S]
    P0 = np.unique(MT[Si[:, None], S[None, :]])
    P1 = np.unique(MT[S[:, None], Si[None, :]])
    unc0 = np.nonzero(~_cover(MT, N, P0))[0]
    unc1 = np.nonzero(~_cover(MT, N, P1))[0]
    if count <= 0 or len(unc0) + len(unc1) == 0:
        return np.empty(0, dtype=np.int32)
    uns = np.concatenate([unc0, unc1]).astype(np.int64)
    sides = np.concatenate([np.zeros(len(unc0), dtype=np.int64), np.ones(len(unc1), dtype=np.int64)])
    pick = rng.integers(len(uns), size=count)
    us = uns[pick]
    ss = sides[pick]
    ru = inv[us]
    s = rest[rng.integers(len(rest), size=count)].astype(np.int64)
    q0 = P0[rng.integers(len(P0), size=count)].astype(np.int64)
    q1 = P1[rng.integers(len(P1), size=count)].astype(np.int64)
    q = np.where(ss == 0, q0, q1)
    x_side0 = MT[MT[s, q], ru]
    x_form_a = MT[MT[us, inv[q]], s]          # u q^-1 s
    x_form_b = MT[MT[q, ru], s]               # q u^-1 s
    x_side1 = np.where(rng.random(count) < 0.5, x_form_a, x_form_b)
    x = np.where(ss == 0, x_side0, x_side1)
    return x.astype(np.int32)


def candidates(MT, inv, S, i, rng, K):
    """Half targeted moves (when an uncovered element exists), half uniformly random values for slot i."""
    N = MT.shape[0]
    rest = np.delete(S, i)
    try:
        T = targeted(MT, inv, S, i, rng, K // 2)
    except Exception:
        T = np.empty(0, dtype=np.int32)
    R = rng.integers(0, N, size=K - len(T)).astype(np.int32)
    X = np.concatenate([T.astype(np.int32), R])
    return X[~np.isin(X, rest)]


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    """Local search over d-subsets of the group, with restarts when stuck.
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
        X = candidates(MT, inv, S, i, rng, K)
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
    """Successive halving over the plan's groups.

    plan: list of (name, builder, S0 or None, weight); fallback: (builder, S) of a valid smaller graph.
    Each round gives every alive group a search slice; the weaker half (by best cost so far) is dropped and
    the slice doubles, so strong groups get long searches that continue from their best S.
    """
    t0 = time.monotonic()
    deadline_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)

    alive = []
    for _name, builder, S0, _w in plan:
        if time.monotonic() >= deadline_all:
            break
        try:
            MT, inv = builder()
        except Exception:
            continue
        alive.append({"MT": MT, "inv": inv,
                      "S": None if S0 is None else np.array(S0, dtype=np.int32),
                      "c": 10 ** 9})

    slice_t = 0.5
    while alive and time.monotonic() < deadline_all:
        for e in alive:
            now = time.monotonic()
            if now >= deadline_all:
                break
            end = min(deadline_all, now + slice_t)
            try:
                S, c = search(e["MT"], e["inv"], d, e["S"], end, rng)
            except Exception:
                e["c"] = 10 ** 9
                continue
            if S is not None and c < e["c"]:
                e["S"], e["c"] = S, c
            if c == 0 and S is not None:
                g = checked(e["MT"], S, d, D)
                if g is not None:
                    return g
        alive.sort(key=lambda e: e["c"])
        if len(alive) > 1:
            alive = alive[:max(1, (len(alive) + 1) // 2)]
        slice_t *= 2

    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ======================================================================================== cell: d6D5
TARGET = (6, 5)      # the (d, D) this plan is for; every other case gets a small always-valid graph

# Fixed non-abelian families just above the threshold 342.
PLAN = [
    ('Heis(3) x Z_13, order 351', lambda: group_times_cyclic(group_heis(3), 13), None, 1),
    ('Heis(7), order 343', lambda: group_heis(7), None, 1),
    ('AGL(1,9) x Z_5, order 360', lambda: group_times_cyclic(group_agl(9), 5), None, 1),
    ('AGL(1,5) x Z_18, order 360', lambda: group_times_cyclic(group_agl(5), 18), None, 1),
]

# Metacyclic groups of orders from 342 to 372 (one per (m, k)); successive halving allocates their time.
for _name, _N, _m, _k, _lam in metacyclic_candidates(342, 372, 14):
    PLAN.append((_name, (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam)), None, 1))

# Valid smaller Haar graph, checked at run time; used only when no plan entry reaches cost 0.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run(d, D, seed, time_limit, PLAN, FALLBACK)
