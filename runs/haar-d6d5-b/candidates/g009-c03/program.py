"""Haar-graph search for the bipartite degree-diameter problem, d=6, D=5 (numpy only).

CONSTRUCTION.  Take a finite group G of order N and a connection set S of 6 elements.  Vertices are
A(g) and B(g) for g in G, with edges A(g) ~ B(s*g) for s in S.  The graph is bipartite, 6-regular,
and has 2N vertices, so N >= 343 beats the record 684.  By the stated criterion, diameter <= 5 holds
iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  The search anneals S (one element replaced per move) to drive
the number of uncovered group elements to zero, using only table lookups.  Non-abelian groups are
tried first, with orders just above the threshold: Heisenberg mod 7 (order 343), Heis(3) x Z_13
(order 351), Heis(3) x Z_14 (order 378), and metacyclic Z_m x| Z_k groups with orders 343..400.

SAFETY.  A valid order-660 Haar graph (checked with lib.is_valid) is computed first and kept as the
fallback.  Any candidate is accepted only after lib.is_valid passes and only if it is larger.
Other (d, D) cases return a small valid graph.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5


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


# ------------------------------------------------------------------------------- Haar helpers

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _fallback(d, D):
    """Valid order-660 Haar graph for d=6, D=5 (checked), else a trivial graph."""
    try:
        MT, _ = group_meta(33, 10, 26)
        g = checked(MT, [0, 179, 116, 180, 47, 306], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ------------------------------------------------------------------------- cost and search

def _cost(MT, inv, S, mark):
    """Uncovered elements of (S^-1 S)^2 plus uncovered elements of (S S^-1)^2.  0 means diameter <= 5."""
    N = MT.shape[0]
    Si = inv[S]
    L = MT[Si[:, None], S[None, :]].ravel()
    L2 = MT[L[:, None], L[None, :]].ravel()
    mark[:] = False
    mark[L2] = True
    c = N - int(np.count_nonzero(mark))
    R = MT[S[:, None], Si[None, :]].ravel()
    R2 = MT[R[:, None], R[None, :]].ravel()
    mark[:] = False
    mark[R2] = True
    return c + N - int(np.count_nonzero(mark))


def _search(MT, inv, deadline, rng):
    """Anneal a 6-element set S until the cost is 0; return a checked (n, edges) or None."""
    N = MT.shape[0]
    mark = np.zeros(N, dtype=bool)
    while time.monotonic() < deadline:
        S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
        cur = _cost(MT, inv, S, mark)
        stall = 0
        T = 0.5
        while cur > 0 and stall < 3000 and time.monotonic() < deadline:
            p = int(rng.integers(DEG))
            x = int(rng.integers(N))
            if x in S:
                stall += 1
                continue
            newS = S.copy()
            newS[p] = x
            c = _cost(MT, inv, newS, mark)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            n, edges = haar_edges(MT, S)
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


def _candidates():
    """Groups with order at least 343 (so 2N > 684), most promising first."""
    out = [("heis", 7, 1), ("tim", 3, 13), ("tim", 3, 14)]
    for NN in range(343, 401):
        for k in range(2, NN):
            if NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 and lam % m != 1:
                    out.append(("meta", m, k, lam))
                    break
    return out[:12]


def _make(c):
    if c[0] == "meta":
        return group_meta(c[1], c[2], c[3])
    if c[0] == "heis":
        return group_heis(c[1])
    return group_times_cyclic(group_heis(c[1]), c[2])


# --------------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        t0 = time.monotonic()
        budget = max(2.0, min(0.7 * time_limit, time_limit - 12.0))
        deadline = t0 + budget
        best = _fallback(d, D)
        rng = np.random.default_rng(seed)
        cands = _candidates()
        for idx, c in enumerate(cands):
            now = time.monotonic()
            if now >= deadline:
                break
            end = now + (deadline - now) / (len(cands) - idx)
            try:
                MT, inv = _make(c)
                N = MT.shape[0]
                if 2 * N <= best[0]:
                    continue
                g = _search(MT, inv, end, rng)
            except Exception:
                continue
            if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                best = g
        return best
    except Exception:
        return trivial(d, D)
