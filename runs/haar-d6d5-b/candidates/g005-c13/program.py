"""Haar-graph search over groups of order 343..362 with a fast word-set cost (numpy only).

CONSTRUCTION.  For a finite group G of order N and a set S of 6 elements, the Haar graph has vertices
A_g = g and B_g = N + g, with edges (g, A) ~ (s*g, B) for s in S.  It is bipartite and 6-regular with 2N vertices.
Its diameter is at most 5 whenever (S^-1 S)^2 = G and (S S^-1)^2 = G.

NEW HELPER: haar_cost(MT, inv, N, S) evaluates these two conditions directly. It forms the word sets
W = {s^-1 t} and U = {s t^-1} (at most 36 elements each), squares them, and counts uncovered group elements.
Each evaluation is a few small numpy operations, so annealing can run many thousands of moves per second.
The parent's cost was a full BFS over the whole graph.

Groups tried: Heisenberg mod 7 (order 343, giving a 686-vertex graph, above the record 684), then nonabelian
metacyclic groups Z_m x|_lam Z_k with orders 344..362. Every result is checked with lib.is_valid before it is kept.
Fallback: the valid order-660 Haar graph, then trivial graphs.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5


# ----------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 128):
        hi = min(N, lo + 128)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def _table_from_coords(elems, mulfun):
    """Group table from an (N, c) coordinate array (identity first) and a vectorised product."""
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


# ----------------------------------------------------------- NEW: fast Haar word-set cost

def haar_cost(MT, inv, N, S):
    """Uncovered group elements: N - |(S^-1 S)^2| plus N - |(S S^-1)^2|.  Zero iff the Haar graph has diameter <= 5."""
    Si = inv[S]
    W = np.unique(MT[Si[:, None], S[None, :]])
    c1 = N - np.unique(MT[W[:, None], W[None, :]]).size
    U = np.unique(MT[S[:, None], Si[None, :]])
    c2 = N - np.unique(MT[U[:, None], U[None, :]]).size
    return int(c1 + c2)


def haar_edges(MT, S):
    """Haar graph edges: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    edges = [(g, N + int(MT[s, g])) for s in S for g in range(N)]
    return 2 * N, edges


# ------------------------------------------------------------------------------- annealing

def anneal(MT, inv, N, deadline, rng):
    """Anneal 6 distinct group elements to haar_cost 0, with restarts.  Returns S (np array) or None."""
    while time.monotonic() < deadline:
        S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
        cur = haar_cost(MT, inv, N, S)
        stall = 0
        T = 1.0
        while cur > 0 and stall < 3000 and time.monotonic() < deadline:
            pos = int(rng.integers(DEG))
            x = int(rng.integers(N))
            if (S == x).any():
                stall += 1
                continue
            newS = S.copy()
            newS[pos] = x
            c = haar_cost(MT, inv, N, newS)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            return S
    return None


# ------------------------------------------------------------------------------ candidates

def candidates(lo=343, hi=362):
    """Heisenberg(7) (order 343) first, then nonabelian metacyclic groups with orders lo..hi, ascending."""
    out = [("heis", 7)]
    for NN in range(lo, hi + 1):
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
    return out


def make_group(c):
    if c[0] == "heis":
        return group_heis(c[1])
    return group_meta(c[1], c[2], c[3])


# ----------------------------------------------------------------------------- fallbacks

def trivial(d, D):
    """A small valid graph for any (d, D), verified; falls back to a single edge or a single vertex."""
    cands = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        cands.append(lambda: lib.projective_plane_incidence(d - 1))
    cands.append(lambda: lib.haar_graph(d, range(d)))
    for f in cands:
        try:
            n, edges = f()
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            pass
    if D >= 1 and d >= 1:
        return 2, [(0, 1)]
    return 1, []


def _fallback(d, D):
    """Valid order-660 Haar graph for d=6, D=5 (checked), else a trivial graph."""
    try:
        MT, _ = group_meta(33, 10, 26)
        S = [0, 179, 116, 180, 47, 306]
        n, edges = haar_edges(MT, S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


# --------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = candidates()
    best = None
    for idx, c in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        end = now + (deadline - now) / (len(cands) - idx)
        try:
            MT, inv = make_group(c)
            N = MT.shape[0]
            S = anneal(MT, inv, N, end, rng)
            if S is None:
                continue
            n, edges = haar_edges(MT, S)
        except Exception:
            continue
        if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
            best = (n, edges)
    if best is not None:
        return best
    return _fallback(d, D)
