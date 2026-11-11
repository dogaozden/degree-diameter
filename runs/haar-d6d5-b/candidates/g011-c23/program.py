"""Haar-graph search for the bipartite degree-diameter problem, d=6, D=5 (numpy + lib only).

CONSTRUCTION.  Take a finite group G of order N and a connection set S of 6 distinct elements.
Vertices (g, A) and (g, B) for g in G, with (g, A) ~ (s*g, B) for s in S.  The graph is bipartite,
6-regular, has 2N vertices, and right multiplication by G is an automorphism, so each side is
vertex-transitive.  Diameter <= 5 holds iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  The cost is the
number of group elements missing from these two sets, so cost 0 means valid.  Any N >= 343 beats the
record 684 (2N = 686).

SEARCH.  Simulated annealing over S (one element replaced per move) on non-abelian groups of order
343..400: Heisenberg mod 7, Heis(3) x Z_13, Heis(3) x Z_14, and metacyclic Z_m x| Z_k.  Each result
is checked with lib.is_valid.  If nothing beats the record, a valid order-660 Haar graph (checked at
run time) is returned.
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
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
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


# ------------------------------------------------------------------------- algebraic cost

def _cost(MT, inv, S, N):
    """Number of group elements missing from (S^-1 S)^2 plus those missing from (S S^-1)^2.  0 means valid."""
    iS = inv[S]
    P = MT[iS[:, None], S[None, :]].ravel()
    Q = MT[P[:, None], P[None, :]].ravel()
    c1 = N - int(np.count_nonzero(np.bincount(Q, minlength=N)))
    P2 = MT[S[:, None], iS[None, :]].ravel()
    Q2 = MT[P2[:, None], P2[None, :]].ravel()
    c2 = N - int(np.count_nonzero(np.bincount(Q2, minlength=N)))
    return c1 + c2


def _search(MT, inv, N, deadline, rng):
    """Anneal the connection set until cost 0; return a checked (n, edges) or None."""
    while time.monotonic() < deadline:
        S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
        cur = _cost(MT, inv, S, N)
        best_local = cur
        stall = 0
        T = 0.5
        while cur > 0 and stall < 3000:
            if time.monotonic() >= deadline:
                return None
            pos = int(rng.integers(DEG))
            x = int(rng.integers(N))
            if np.any(S == x):
                stall += 1
                continue
            newS = S.copy()
            newS[pos] = x
            c = _cost(MT, inv, newS, N)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                if cur < best_local:
                    best_local = cur
                    stall = 0
                else:
                    stall += 1
            else:
                stall += 1
        if cur == 0:
            n, edges = haar_edges(MT, S)
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


# ------------------------------------------------------------------------------- candidate groups

def _candidates():
    """Non-abelian groups of order 343..400, ordered by size, with the most promising first."""
    out = [("heis", 7, 0), ("tc", 3, 13)]
    for NN in range(343, 401):
        if NN in (351,):
            continue
        for k in range(2, NN):
            if NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            found = False
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 and lam % m != 1:
                    out.append(("meta", m, k, lam))
                    found = True
                    break
            if found and len(out) >= 14:
                break
        if len(out) >= 14:
            break
    out.append(("tc", 3, 14))
    return out


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
    t0 = time.monotonic()
    budget = max(2.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = _candidates()
    best = None
    for idx, c in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = _make(c)
            N = MT.shape[0]
            g = _search(MT, inv, N, end, rng)
        except Exception:
            continue
        if g is not None and (best is None or g[0] > best[0]):
            best = g
    if best is not None:
        return best
    return _fallback(d, D)
