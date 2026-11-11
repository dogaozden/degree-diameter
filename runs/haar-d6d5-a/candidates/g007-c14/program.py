"""Voltage lifts over a 2k-vertex bipartite base (k per side, degree 6) with a non-abelian group G.

NEW CONSTRUCTION.  The parent searched Haar graphs only (k = 1: one A and one B base vertex joined by 6 parallel
darts), which caps the order at 2|G|.  Here the base has k A-vertices and k B-vertices, joined by six perfect
matchings sigma_1..sigma_6, so every base vertex has degree 6.  Dart t at A_i carries a voltage v[t, i] in G, and the
lift is (A_i, x) ~ (B_{sigma_t(i)}, x * v[t, i]).  The lift has 2 k |G| vertices.

Left multiplication by G is an automorphism that acts regularly on each fibre, so the diameter is at most D iff every
base class reaches all of the graph within radius D from its identity lift.  The cost is the number of
(source, vertex) pairs at distance > D, from 2k sources, computed with numpy BFS.  Annealing changes one voltage or
swaps two entries of a matching.  Any valid lift with more than 684 vertices is kept.

Fallbacks: the parent's valid order-330 Haar graph (660 vertices), then K_{d,d} (or the Heawood graph for d=3, D=3).
Every returned graph is checked with lib.is_valid.
"""
import itertools
import math
import time

import numpy as np

import lib

DEG = 6
TARGET = (6, 5)


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


def group_sl2(p):
    """SL(2, p) for a prime p, matrices (a, b, c, d), order p(p^2-1), identity first."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q):
    """AGL(1, q) = GF(q) x| GF(q)^*, maps t -> a*t + b, identity first."""
    F = lib.GF(q)
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in range(1, q) if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def metacyclic_candidates(lo, hi, limit):
    """Non-abelian metacyclic Z_m x|_lam Z_k with lo <= m*k <= hi (one lam per (m, k)), smallest order first."""
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


# ------------------------------------------------------------------------------------- voltage lifts

def make_nbr(MT, inv, k, P, V):
    """Neighbour table (2kN x DEG).  A-vertex i*N+x is index i*N+x, B-vertex j*N+y is index kN+j*N+y.
    P[t] is the matching sigma_t (a permutation of range(k)), V[t, i] the voltage of dart t at A_i."""
    N = MT.shape[0]
    x = np.arange(N)
    nb = np.empty((2 * k * N, DEG), dtype=np.int64)
    for i in range(k):
        for t in range(DEG):
            nb[i * N:(i + 1) * N, t] = k * N + int(P[t, i]) * N + MT[x, int(V[t, i])]
    Pinv = np.argsort(P, axis=1)
    for j in range(k):
        for t in range(DEG):
            i = int(Pinv[t, j])
            nb[k * N + j * N:k * N + (j + 1) * N, t] = i * N + MT[x, int(inv[V[t, i]])]
    return nb


def cost_of(nb, N, k, D):
    """Number of (source, vertex) pairs at distance > D, over the 2k base-class identity sources."""
    n = 2 * k * N
    srcs = np.array([i * N for i in range(k)] + [k * N + j * N for j in range(k)], dtype=np.int64)
    S = len(srcs)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), srcs] = True
    for _ in range(D):
        R = R | R[:, nb].any(axis=2)
    return S * n - int(R.sum())


def lift_graph(MT, inv, k, P, V):
    """Return (n, sorted edge list) of the lift."""
    N = MT.shape[0]
    nb = make_nbr(MT, inv, k, P, V)
    edges = set()
    for a in range(k * N):
        for b in nb[a]:
            edges.add((a, int(b)))
    return 2 * k * N, sorted(edges)


def anneal(MT, inv, k, deadline, rng, D, temp=1.0, patience=3000):
    """Simulated annealing over matchings and voltages.  Returns (best cost, P, V)."""
    N = MT.shape[0]

    def fresh():
        P = np.array([rng.permutation(k) for _ in range(DEG)], dtype=np.int64)
        V = rng.integers(0, N, size=(DEG, k)).astype(np.int64)
        return P, V

    P, V = fresh()
    cur = cost_of(make_nbr(MT, inv, k, P, V), N, k, D)
    best = (cur, P, V)
    since = 0
    while cur > 0 and time.monotonic() < deadline:
        if k > 1 and rng.random() < 0.3:
            t = int(rng.integers(DEG))
            a, b = rng.choice(k, 2, replace=False)
            P2 = P.copy()
            P2[t, a], P2[t, b] = P[t, b], P[t, a]
            V2 = V
        else:
            P2 = P
            V2 = V.copy()
            t = int(rng.integers(DEG))
            i = int(rng.integers(k))
            V2[t, i] = int(rng.integers(N))
        c = cost_of(make_nbr(MT, inv, k, P2, V2), N, k, D)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            P, V, cur = P2, V2, c
            if cur < best[0]:
                best = (cur, P, V)
                since = 0
        since += 1
        if since > patience:
            P, V = fresh()
            cur = cost_of(make_nbr(MT, inv, k, P, V), N, k, D)
            since = 0
    return best


# ----------------------------------------------------------------------------------- fallbacks

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def haar_fallback():
    """Valid Haar graph of order 330 (660 vertices), claimed valid by the parent; checked before use."""
    MT, _ = group_meta(33, 10, 26)
    return haar_edges(MT, [0, 179, 116, 180, 47, 306])


def trivial(d, D):
    """Always-valid small graph for any (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    if D >= 2 and d >= 1:
        return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]
    if D >= 1 and d >= 1:
        return 2, [(0, 1)]
    return 1, []


# ----------------------------------------------------------------------------------------- the plan

def _plan():
    """Candidates (V, k, name, builder) with V = 2*k*|G| > 684, sorted by V ascending."""
    P_ = []

    def add(k, N, name, builder):
        V = 2 * k * N
        if V > 684:
            P_.append((V, k, name, builder))

    add(1, 343, 'Heisenberg 7', lambda: group_heis(7))
    for m, kk, lam in metacyclic_candidates(343, 360, 2):
        add(1, m * kk, f'meta {m}/{kk}/{lam}', lambda m=m, kk=kk, lam=lam: group_meta(m, kk, lam))
    add(2, 342, 'AGL(1,19)', lambda: group_agl(19))
    add(2, 272, 'AGL(1,17)', lambda: group_agl(17))
    for m, kk, lam in metacyclic_candidates(172, 180, 2):
        add(2, m * kk, f'meta {m}/{kk}/{lam}', lambda m=m, kk=kk, lam=lam: group_meta(m, kk, lam))
    add(3, 120, 'SL(2,5)', lambda: group_sl2(5))
    for m, kk, lam in metacyclic_candidates(115, 124, 2):
        add(3, m * kk, f'meta {m}/{kk}/{lam}', lambda m=m, kk=kk, lam=lam: group_meta(m, kk, lam))
    add(4, 156, 'AGL(1,13)', lambda: group_agl(13))
    add(4, 110, 'AGL(1,11)', lambda: group_agl(11))
    for m, kk, lam in metacyclic_candidates(86, 100, 2):
        add(4, m * kk, f'meta {m}/{kk}/{lam}', lambda m=m, kk=kk, lam=lam: group_meta(m, kk, lam))
    for m, kk, lam in metacyclic_candidates(58, 70, 2):
        add(6, m * kk, f'meta {m}/{kk}/{lam}', lambda m=m, kk=kk, lam=lam: group_meta(m, kk, lam))
    P_.sort(key=lambda e: e[0])
    return P_


PLAN = _plan()


# ------------------------------------------------------------------------------------------- driver

def run(d, D, seed, time_limit, plan):
    """Keep the largest valid graph found; a candidate is skipped if its order cannot beat the current best."""
    t0 = time.monotonic()
    deadline = t0 + max(1.0, 0.8 * time_limit - 1.0)
    rng = np.random.default_rng(seed)

    best = None
    try:
        n, edges = haar_fallback()
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass
    best_n = best[0] if best is not None else 0

    for idx, (V, k, name, builder) in enumerate(plan):
        now = time.monotonic()
        if now >= deadline:
            break
        left = len(plan) - idx
        if V <= best_n:
            continue
        end = now + (deadline - now) / left
        try:
            MT, inv = builder()
            c, P, Vv = anneal(MT, inv, k, end, rng, D)
            if c == 0:
                n, edges = lift_graph(MT, inv, k, P, Vv)
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best, best_n = (n, edges), n
        except Exception:
            continue

    if best is not None:
        return best
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        n, edges = run(d, D, seed, time_limit, PLAN)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)
