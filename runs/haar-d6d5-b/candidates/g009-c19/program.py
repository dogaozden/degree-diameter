"""Haar-graph search at orders just above the record (d=6, D=5), with a safe fallback.

CONSTRUCTION.  Take a finite group G of order N and a connection set S of 6 distinct
elements.  Vertices A(g) and B(g) for g in G, with edges A(g) ~ B(s*g) for s in S.
The graph is bipartite, 6-regular, and has 2N vertices.  Left multiplication by any
h in G is an automorphism, so the diameter is at most 5 iff BFS of radius 5 from
A(e) and from B(e) reaches every vertex.  COST(S) counts the unreached vertices.
Valid iff COST = 0.  2N >= 690 beats the record 684, so N >= 345 is the target.

Search: simulated annealing over S (one element replaced per move) with restarts,
over non-abelian metacyclic groups and Heis(3) x Z_k of orders 345..372.  Any
result is checked with lib.is_valid before it is returned.  If nothing is found,
the valid order-660 Haar graph (checked at run time) or a trivial valid graph is returned.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5
MIN_N = 345   # 2 * 345 = 690 > 684 (record)
MAX_N = 372


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


# ------------------------------------------------------------------------- Haar graph and cost

def _nbr(MT, inv, S):
    """Neighbour array (2N x DEG).  Rows 0..N-1 are A(g) with neighbours N + s*g; rows N..2N-1 are B(h)
    with neighbours inv(s)*h (A-indices)."""
    N = MT.shape[0]
    g = np.arange(N, dtype=np.int64)
    nb = np.empty((2 * N, DEG), dtype=np.int64)
    for c in range(DEG):
        s = int(S[c])
        nb[:N, c] = N + MT[s, g]
        nb[N:, c] = MT[int(inv[s]), g]
    return nb


def _cost(nb, N):
    """Vertices not reached within DIAM steps from A(e) and B(e) (0 means valid)."""
    n = 2 * N
    total = 0
    for src in (0, N):
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(DIAM):
            nx = nb[fr].ravel()
            nx = nx[~seen[nx]]
            if nx.size == 0:
                break
            nx = np.unique(nx)
            seen[nx] = True
            fr = nx
        total += n - int(np.count_nonzero(seen))
    return total


def _anneal(MT, inv, N, deadline, rng):
    """Anneal a connection set until cost 0 (with restarts); return a checked (n, edges) or None."""
    while time.monotonic() < deadline:
        S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
        cur = _cost(_nbr(MT, inv, S), N)
        stall = 0
        T = 0.4
        while time.monotonic() < deadline and cur > 0 and stall < 3000:
            pos = int(rng.integers(DEG))
            x = int(rng.integers(N))
            if np.any(S == x):
                stall += 1
                continue
            newS = S.copy()
            newS[pos] = x
            c = _cost(_nbr(MT, inv, newS), N)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            nb = _nbr(MT, inv, S)
            edges = [(u, int(v)) for u in range(N) for v in nb[u]]
            if lib.is_valid(2 * N, edges, DEG, DIAM):
                return 2 * N, edges
    return None


def _candidates(lo, hi):
    """Non-abelian metacyclic groups of orders in [lo, hi] (up to two per order), plus Heis(3) x Z_k."""
    out = []
    for NN in range(lo, hi + 1):
        found = 0
        for k in range(2, NN):
            if NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            lam = next((l for l in range(2, m) if math.gcd(l, m) == 1 and pow(l, k, m) == 1), None)
            if lam is not None:
                out.append(("meta", m, k, lam))
                found += 1
            if found >= 2:
                break
        if NN % 27 == 0 and NN // 27 >= 2:
            out.append(("heis", NN // 27))
    return out


def _make(c):
    if c[0] == "meta":
        return group_meta(c[1], c[2], c[3])
    return group_times_cyclic(group_heis(3), c[1])


# --------------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(3.0, min(45.0, time_limit - 12.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = _candidates(MIN_N, MAX_N)
    for idx, c in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = _make(c)
            N = MT.shape[0]
            if 2 * N <= 684:
                continue
            g = _anneal(MT, inv, N, end, rng)
        except Exception:
            continue
        if g is not None:
            return g
    return _fallback(d, D)
