"""Haar-graph search for the diameter-5 bipartite degree-diameter problem (numpy + lib only).

A Haar graph over a group G with connection set S (|S| = d, 0 in S WLOG) has 2|G| vertices and
diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G. The cost counts uncovered elements.

New in this version:
  * Product-word moves: besides random group elements, candidate replacements are words
    s_a^-1 s_b and s_a s_b drawn from the current set, so the search moves within the
    structure the covering condition is built from.
  * Round-robin over many groups of order 2001..2100 (metacyclic plus SL(2,7)xZ6,
    Heis(7)xZ6, AGL(1,13)xZ13), with a time slice per group, instead of one fixed group.
  * Every returned graph is checked with lib.is_valid. Fallbacks are a verified Haar graph
    and K_{d,d}.
"""
import itertools
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a,j)(b,l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def _table_from_coords(elems, mulfun):
    """Table of a group given by an (N, c) coordinate array (row 0 = identity) and a vectorised product."""
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
    """Heisenberg group mod p (order p^3)."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for prime p, order p(p^2-1)."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p,
                         (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q):
    """AGL(1, q) = GF(q) x| GF(q)^*, q a prime power."""
    F = lib.GF(q)
    H = [a for a in range(1, q)]
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


# ----------------------------------------------------------------------------- cost and moves

def cost(MT, inv, S):
    """Uncovered elements over both sides: T0 = S^-1 S and T1 = S S^-1 must satisfy T^2 = G."""
    N = MT.shape[0]
    Si = inv[S]
    tot = 0
    for P in (MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()):
        P = np.unique(P)
        cov = np.zeros(N, dtype=bool)
        cov[MT[P[:, None], P[None, :]].ravel()] = True
        tot += N - int(cov.sum())
    return tot


def candidates(MT, inv, S, rng, K):
    """Replacement candidates: random elements, plus product words s_a^-1 s_b and s_a s_b of the current set."""
    N = MT.shape[0]
    d = len(S)
    out = []
    for _ in range(K):
        r = rng.random()
        if r < 0.4:
            x = int(rng.integers(N))
        else:
            a, b = (int(v) for v in rng.integers(d, size=2))
            if r < 0.7:
                x = int(MT[inv[S[a]], S[b]])
            else:
                x = int(MT[S[a], S[b]])
        out.append(x)
    return out


def anneal(MT, inv, d, deadline, rng, patience=2500, K=12, temp=0.45):
    """Annealing with restarts on d-subsets containing 0 (0 WLOG by right-translation). Returns (best S, best cost)."""
    N = MT.shape[0]
    gbest, gbestc = None, 10 ** 9
    while time.monotonic() < deadline and gbestc > 0:
        S = np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int64)
        cur = cost(MT, inv, S)
        if cur < gbestc:
            gbest, gbestc = S.copy(), cur
        stall = 0
        while cur > 0 and stall < patience and time.monotonic() < deadline:
            i = int(rng.integers(1, d))
            present = set(S.tolist())
            cand = [x for x in candidates(MT, inv, S, rng, K) if x not in present]
            if not cand:
                stall += 1
                continue
            cs = []
            for x in cand:
                S2 = S.copy()
                S2[i] = x
                cs.append(cost(MT, inv, S2))
            vals = np.array(cs, dtype=float) + rng.random(len(cs)) * 0.5
            j = int(np.argmin(vals))
            c = cs[j]
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                S[i] = cand[j]
                cur = c
                if cur < gbestc:
                    gbest, gbestc = S.copy(), cur
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
    return gbest, gbestc


# ----------------------------------------------------------------------------- graphs

def haar_edges(MT, S):
    """Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S if lib.is_valid accepts it, else None."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def complete_bipartite(d, D):
    """K_{d,d}: max degree d, diameter 2 (valid whenever D >= 2)."""
    n = 2 * d
    return n, [(i, d + j) for i in range(d) for j in range(d)]


def trivial(d, D):
    """Small valid graph for any other (d, D), always verified."""
    cands = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        cands.append(lib.projective_plane_incidence(d - 1))
    cands.append(lib.haar_graph(d, range(d)))
    cands.append(complete_bipartite(d, D))
    for n, edges in cands:
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return 2, [(0, 1)]


# ----------------------------------------------------------------------------- target case

TARGET = (10, 5)
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def metacyclic_specs(lo, hi):
    """Specs ('meta', m, k, lam) for Z_m x|_lam Z_k, lo <= m*k <= hi, lam != 1, lam^k = 1 mod m."""
    out = []
    for k in range(2, 13):
        for m in range(max(2, -(-lo // k)), hi // k + 1):
            if not (lo <= m * k <= hi):
                continue
            found = 0
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append(('meta', m, k, lam))
                    found += 1
                    if found >= 2:
                        break
    return out


def make_builder(spec):
    if spec[0] == 'meta':
        _, m, k, lam = spec
        return lambda: group_meta(m, k, lam)
    if spec[0] == 'sl2':
        return lambda: group_times_cyclic(group_sl2(7), 6)
    if spec[0] == 'heis':
        return lambda: group_times_cyclic(group_heis(7), 6)
    if spec[0] == 'agl':
        return lambda: group_times_cyclic(group_agl(13), 13)
    raise ValueError(spec)


def run_target(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.78 * time_limit
    rng = np.random.default_rng(seed)
    specs = metacyclic_specs(2001, 2100) + [('sl2',), ('heis',), ('agl',)]
    order = rng.permutation(len(specs))
    slice_len = 4.0
    k = 0
    while time.monotonic() < end - 0.5:
        spec = specs[int(order[k % len(order)])]
        k += 1
        deadline = min(end, time.monotonic() + slice_len)
        try:
            MT, inv = make_builder(spec)()
        except Exception:
            continue
        S, c = anneal(MT, inv, d, deadline, rng)
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None:
                return g
    try:
        MT, inv = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run_target(d, D, seed, time_limit)
