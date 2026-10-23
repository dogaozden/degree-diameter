"""Haar-graph search for the bipartite degree-diameter problem, d=6, D=5 (numpy only).

CONSTRUCTION.  Take a non-abelian metacyclic group G = Z_m x|_lam Z_k of order N and a connection set S of
6 distinct elements.  Vertices are A(g) and B(g) for g in G, with edges A(g) ~ B(s*g) for s in S.  Right
multiplication by any h in G is an automorphism, so the A-side and the B-side are each vertex-transitive.
Hence the diameter is at most 5 iff BFS of radius 5 from A(e) and from B(e) reaches every vertex.  The graph has
2N vertices, so N >= 343 beats the record 684.

This replaces the previous 4-orbit bi-Cayley search, which never reached cost 0 in budget.  It uses the
2-orbit Haar construction, which is the one that produced the diameter-5 records for d = 7, 8, 9.

COST(S) = number of vertices not reached within 5 steps from A(e) and B(e) (0 means valid).  Search is
simulated annealing with single-element replacement moves and restarts.  Candidate groups are tried in
increasing order of order, and each gets a time slice.  Any found graph is checked with lib.is_valid.
If nothing is found, the valid order-660 Haar graph (checked at run time) or a trivial graph is returned.
"""
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5
MIN_ORDER = 343   # 2 * 343 = 686 > 684 (record)
MAX_ORDER = 430


# ----------------------------------------------------------------------------- group tables

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
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


# ------------------------------------------------------------------------- Haar helpers

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


# ------------------------------------------------------------------------- cost

def _nb(MT, inv, S, N):
    """Neighbour array (2N x DEG).  A(g) = g, B(h) = N + h.
    A(g) ~ B(s*g) for s in S, so B(h) ~ A(inv[s]*h)."""
    nb = np.empty((2 * N, DEG), dtype=np.int64)
    nb[:N] = N + MT[S, :].T
    nb[N:] = MT[inv[S], :].T
    return nb


def _bfs_uncovered(nb, src, n):
    """Number of vertices not reached from src within DIAM steps."""
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
    return n - int(np.count_nonzero(seen))


def _cost(nb, N):
    """Uncovered count from A(e) and B(e).  Zero means diameter <= DIAM."""
    n = 2 * N
    return _bfs_uncovered(nb, 0, n) + _bfs_uncovered(nb, N, n)


# ------------------------------------------------------------------------- search

def _anneal(MT, inv, N, deadline, rng):
    """Anneal a connection set until cost 0, restarting when stuck.  Returns a checked (n, edges) or None."""
    while time.monotonic() < deadline:
        S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
        cur = _cost(_nb(MT, inv, S, N), N)
        stall = 0
        T = 1.0
        it = 0
        while cur > 0 and stall < 3000 and time.monotonic() < deadline:
            pos = int(rng.integers(DEG))
            x = int(rng.integers(N))
            if x in S:
                continue
            newS = S.copy()
            newS[pos] = x
            c = _cost(_nb(MT, inv, newS, N), N)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
            it += 1
            if it % 2000 == 0:
                T = max(0.3, T * 0.95)
        if cur == 0:
            n, edges = haar_edges(MT, [int(s) for s in S])
            if lib.is_valid(n, edges, DEG, DIAM):
                return n, edges
    return None


def _candidates():
    """Non-abelian metacyclic groups Z_m x|_lam Z_k of order in [MIN_ORDER, MAX_ORDER], smallest order first."""
    out = []
    for N in range(MIN_ORDER, MAX_ORDER + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            found = 0
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((m, k, lam))
                    found += 1
                    if found >= 2:
                        break
    return out


# --------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        t0 = time.monotonic()
        budget = max(2.0, min(0.75 * time_limit, time_limit - 12.0))
        deadline = t0 + budget
        rng = np.random.default_rng(seed)
        cands = _candidates()
        best = None
        for idx, (m, k, lam) in enumerate(cands):
            now = time.monotonic()
            if now >= deadline:
                break
            rem = deadline - now
            slice_t = min(rem, max(1.5, rem * 0.15))
            try:
                MT, inv = group_meta(m, k, lam)
                N = MT.shape[0]
                g = _anneal(MT, inv, N, now + slice_t, rng)
            except Exception:
                continue
            if g is not None and (best is None or g[0] > best[0]):
                best = g
        if best is not None and lib.is_valid(best[0], best[1], d, D):
            return best
    except Exception:
        pass
    return _fallback(d, D)
