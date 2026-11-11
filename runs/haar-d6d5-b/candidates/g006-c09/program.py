"""Haar-graph search over groups of order 343 and up (d=6, D=5), with a fast exact cost.

CONSTRUCTION. A Haar graph H(G, S) has vertices A_g and B_g for g in G, with edges A_g ~ B_{s*g} for s in S,
|S| = 6. It is bipartite and 6-regular on 2|G| vertices. Its diameter is at most 5 whenever
(S^-1 S)^2 = G and (S S^-1)^2 = G. This is a sufficient condition, and the cost below counts how far each
side is from it. |G| = 343 (Heisenberg mod 7, or Z_49 x| Z_7) gives 686 > 684 vertices, which beats the record.

COST(S) = (|G| - |(S^-1 S)^2|) + (|G| - |(S S^-1)^2|). Cost 0 means the sufficient condition holds.
Search: simulated annealing over the six entries of S, with restarts. Each found graph is checked with
lib.is_valid before it is returned. If nothing is found in the budget, the valid order-660 Haar graph
(checked at run time) or a trivial valid graph is returned.
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
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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


# ------------------------------------------------------------------------------- Haar graph helpers

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def _cost(MT, inv, N, S):
    """Uncovered group elements for (S^-1 S)^2 and (S S^-1)^2. Zero means the sufficient diameter-5 condition holds."""
    iS = inv[S]
    T1 = np.unique(MT[iS[:, None], S[None, :]])
    Q1 = np.unique(MT[T1[:, None], T1[None, :]])
    T2 = np.unique(MT[S[:, None], iS[None, :]])
    Q2 = np.unique(MT[T2[:, None], T2[None, :]])
    return (N - Q1.size) + (N - Q2.size)


def _search(MT, inv, N, deadline, rng):
    """Anneal the connection set S of size DEG until cost 0; return a checked (n, edges) or None."""
    while time.monotonic() < deadline:
        S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
        cur = _cost(MT, inv, N, S)
        stall = 0
        T = 0.6
        while cur > 0 and stall < 3000 and time.monotonic() < deadline:
            pos = int(rng.integers(DEG))
            x = int(rng.integers(N))
            if x in S:
                stall += 1
                continue
            S2 = S.copy()
            S2[pos] = x
            c = _cost(MT, inv, N, S2)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = S2, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            n, edges = haar_edges(MT, S)
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


def _candidates():
    """Groups of order 343 and up: Heisenberg mod 7, Heis(3) x Z_13, and non-abelian metacyclic groups."""
    out = [(343, ("heis", 7, 0, 0)), (351, ("hz", 3, 13, 0))]
    for NN in range(343, 373):
        for k in range(2, NN):
            if NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 and lam % m != 1:
                    out.append((NN, ("meta", m, k, lam)))
                    break
    out.sort(key=lambda t: t[0])
    return [c for _, c in out[:24]]


def _make(c):
    if c[0] == "meta":
        return group_meta(c[1], c[2], c[3])
    if c[0] == "heis":
        return _finish(group_heis(c[1]).__getitem__(0)) if False else group_heis(c[1])
    return group_times_cyclic(group_heis(3), c[2])


# ------------------------------------------------------------------------------------ fallbacks

def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    cands = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        cands.append(lambda: lib.projective_plane_incidence(d - 1))
    cands.append(lambda: lib.haar_graph(d, range(d)))
    for f in cands:
        try:
            n, e = f()
            if lib.is_valid(n, e, d, D):
                return n, e
        except Exception:
            pass
    return 2, [(0, 1)]


def _fallback(d, D):
    """Valid order-660 Haar graph for d=6, D=5 (checked), else a trivial graph."""
    try:
        MT, _ = group_meta(33, 10, 26)
        n, edges = haar_edges(MT, [0, 179, 116, 180, 47, 306])
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


# --------------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = _candidates()
    best = None
    for idx, c in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        remaining = len(cands) - idx
        end = now + min(12.0, (deadline - now) / remaining)
        try:
            MT, inv = _make(c)
            N = MT.shape[0]
            g = _search(MT, inv, N, end, rng)
        except Exception:
            continue
        if g is not None and (best is None or g[0] > best[0]):
            best = g
    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return _fallback(d, D)
