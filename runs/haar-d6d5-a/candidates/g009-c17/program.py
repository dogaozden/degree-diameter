"""Haar-graph search for the bipartite degree-diameter problem, diameter 5 (numpy only).

Haar graph of a group G with connection set S (|S| = d): vertices (g, A) and (g, B), edges (g, A) ~ (s*g, B).
It is bipartite, d-regular, has 2|G| vertices, and has diameter <= 5 iff
    (S^-1 S)^2 = G  and  (S S^-1)^2 = G.
cost(S) counts the uncovered group elements, so cost 0 means a valid graph.

CHANGE IN THIS VERSION (bold): the group pool is much wider and the time policy is a race.
  * Pool: metacyclic Z_m x| Z_k of orders 342..470, AGL(1,q) subgroups GF(q) x| C_k of order q*k
    (q a prime power, k | q-1), Heisenberg groups mod 3, 5, 7 (times Z_k), and AGL(1,q) x Z_k for small q.
  * Phase 1 screens every candidate (ascending order) with a short annealing budget.
  * Phase 2 repeatedly warm-starts the most promising still-invalid candidate whose order exceeds the
    best valid order found so far, so time goes to near misses that could beat the record.
  * Every returned graph is checked with lib.is_valid. Fallbacks: a precomputed valid Haar graph
    (order 330), then a small always-valid graph.
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
    """Heisenberg group mod p (upper unitriangular 3x3), order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)   # (0,0,0) is first

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k: maps t -> a*t + b with a in the order-k subgroup of GF(q)^* (default k = q-1, AGL(1,q))."""
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
    """Score every single-slot replacement of S.  Returns (best cost, best S)."""
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
    """Annealing over d-subsets of the group.  With a start set S0: scan its 1-swap neighbours first, then anneal.
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
    """Small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def trivial_safe(d, D):
    """trivial(d, D) if it passes lib.is_valid, otherwise a single edge (valid whenever d, D >= 1)."""
    try:
        n, edges = trivial(d, D)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return 2, [(0, 1)]


# ======================================================================================== target d6D5
TARGET = (6, 5)


def metacyclic_candidates(lo, hi, per_order=2, limit=12):
    """Non-abelian Z_m x|_lam Z_k groups of order N in [lo, hi], smallest order first: (N, m, k, lam)."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            found = 0
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or pow(lam, k, m) != 1 % m:
                    continue
                out.append((N, m, k, lam))
                found += 1
                if found >= per_order:
                    break
    return out[:limit]


def make_candidates(lo=342, hi=470, cap=36):
    """Wide pool of non-abelian groups with orders in [lo, hi], sorted by order: (order, name, builder)."""
    c = []
    for N, m, k, lam in metacyclic_candidates(lo, hi, per_order=2, limit=60):
        c.append((N, f"meta Z{m}x|Z{k} lam={lam}", lambda m=m, k=k, lam=lam: group_meta(m, k, lam)))
    # GF(q) x| C_k subgroups of the affine group, q a prime power
    for q in range(7, 200):
        if not lib.is_prime_power(q):
            continue
        for k in range(2, q):
            N = q * k
            if (q - 1) % k == 0 and lo <= N <= hi:
                c.append((N, f"AGL-sub GF({q}) k={k}", lambda q=q, k=k: group_agl(q, k)))
    # Heisenberg groups, alone and times Z_k
    for p in (3, 5, 7):
        base = p ** 3
        for k in range(1, hi // base + 1):
            N = base * k
            if lo <= N <= hi:
                if k == 1:
                    c.append((N, f"Heis({p})", lambda p=p: group_heis(p)))
                else:
                    c.append((N, f"Heis({p}) x Z{k}", lambda p=p, k=k: group_times_cyclic(group_heis(p), k)))
    # AGL(1,q) times Z_k for small q
    for q in (5, 7, 8, 9):
        base = q * (q - 1)
        for kk in range(2, hi // base + 1):
            N = base * kk
            if lo <= N <= hi:
                c.append((N, f"AGL(1,{q}) x Z{kk}", lambda q=q, kk=kk: group_times_cyclic(group_agl(q), kk)))
    c.sort(key=lambda t: t[0])
    return c[:cap]


FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])   # valid Haar graph, order 330


def race(d, D, rng, cands, end_all):
    """Phase 1 screens all candidates; phase 2 warm-starts the best invalid ones above the best valid order.
    Returns the largest checked valid graph found, or None."""
    best_g, best_N = None, 0
    states = {}   # idx -> [S, cost]

    now = time.monotonic()
    per = max(0.2, (end_all - now) * 0.55 / max(1, len(cands)))
    for idx, (N, name, builder) in enumerate(cands):
        if time.monotonic() >= end_all:
            break
        if N <= best_N:
            continue
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, None, min(end_all, time.monotonic() + per), rng)
        except Exception:
            continue
        if S is None:
            continue
        states[idx] = [S, c]
        if c == 0:
            g = checked(MT, S, d, D)
            if g is not None and N > best_N:
                best_g, best_N = g, N

    while time.monotonic() < end_all - 0.5:
        live = [i for i, (S, c) in states.items() if c > 0 and cands[i][0] > best_N]
        if not live:
            break
        i = min(live, key=lambda t: (states[t][1], rng.random()))
        N, name, builder = cands[i]
        sl = min(3.0, max(0.3, end_all - time.monotonic()))
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, states[i][0], min(end_all, time.monotonic() + sl), rng)
        except Exception:
            del states[i]
            continue
        if S is not None and c <= states[i][1]:
            states[i] = [S, c]
        if c == 0:
            g = checked(MT, S, d, D)
            if g is not None and N > best_N:
                best_g, best_N = g, N
    return best_g


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial_safe(d, D)
    t0 = time.monotonic()
    end_all = t0 + 0.72 * time_limit
    rng = np.random.default_rng(seed)
    g = None
    try:
        g = race(d, D, rng, make_candidates(), end_all)
    except Exception:
        g = None
    if g is None:
        try:
            MT, inv = FALLBACK[0]()
            g = checked(MT, FALLBACK[1], d, D)
        except Exception:
            g = None
    if g is None:
        g = trivial_safe(d, D)
    return g
