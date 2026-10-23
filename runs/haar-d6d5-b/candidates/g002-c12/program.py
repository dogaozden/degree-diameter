"""Haar-graph search for d=6, D=5 over non-abelian groups of order >= 343 (numpy only).

CONSTRUCTION.  A Haar graph on two copies of a group G (|G| = N): A-vertex g joins B-vertex s*g for each s in S,
|S| = 6.  The graph is bipartite, 6-regular, has 2N vertices, and right multiplication is an automorphism that
is transitive on each side.  So its diameter is at most 5 iff BFS of radius 5 from A_e and from B_e reaches
every vertex.  This check is exact and is used directly as the cost.

Targets: |G| >= 343 gives 2N >= 686 > 684 (record).  Candidates are Heisenberg(7) (order 343), Z_49 x| Z_7
(order 343), and metacyclic groups of orders 344..400.  Annealing over S (one element replaced per move, Metropolis
acceptance, restarts when stalled) runs round-robin over the candidates.  Any result is checked with lib.is_valid
before it is kept.  If nothing valid is found, a checked order-660 Haar graph or a trivial graph is returned.
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
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
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
    """Multiplication table from an (N, c) coordinate array (element 0 = identity) and a vectorised product."""
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


# ------------------------------------------------------------------------- Haar graph and exact cost

def _nbr(MT, inv, S):
    """Neighbour array (2N x DEG).  A-vertex g is index g, B-vertex h is index N+h.
    A-vertex g ~ B-vertex s*g; B-vertex h ~ A-vertex s^-1*h."""
    A = MT[S].T.astype(np.int64)                    # (N, DEG): values are B-indices (offset added below)
    B = MT[inv[S]].T.astype(np.int64)               # (N, DEG): A-indices
    N = MT.shape[0]
    return np.vstack([A + N, B])


def _unreached(nbr, src):
    """Number of vertices not within DIAM steps of src."""
    n = nbr.shape[0]
    seen = np.zeros(n, dtype=bool)
    seen[src] = True
    fr = np.array([src], dtype=np.int64)
    for _ in range(DIAM):
        nx = nbr[fr].ravel()
        nx = np.unique(nx[~seen[nx]])
        if nx.size == 0:
            break
        seen[nx] = True
        fr = nx
    return n - int(np.count_nonzero(seen))


def _cost(nbr):
    """Zero iff diameter <= DIAM.  Right multiplication is an automorphism that is transitive on each side,
    so BFS from A_e and from B_e covers every pair."""
    N = nbr.shape[0] // 2
    return _unreached(nbr, 0) + _unreached(nbr, N)


def _anneal(MT, inv, deadline, rng):
    """Anneal a 6-element set S until the Haar graph has diameter <= DIAM; return S or None at the deadline."""
    N = MT.shape[0]
    while time.monotonic() < deadline:
        S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
        cur = _cost(_nbr(MT, inv, S))
        stall = 0
        T = 0.7
        while cur > 0 and stall < 2500:
            if time.monotonic() >= deadline:
                return None
            pos = int(rng.integers(DEG))
            x = int(rng.integers(N))
            if (S == x).any():
                stall += 1
                continue
            newS = S.copy()
            newS[pos] = x
            c = _cost(_nbr(MT, inv, newS))
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S, cur = newS, c
                stall = 0 if delta < 0 else stall + 1
            else:
                stall += 1
        if cur == 0:
            return S
    return None


def _graph(MT, S):
    """Edge list of the Haar graph: A-vertex g is g, B-vertex h is N+h, edges (g, N + s*g)."""
    N = MT.shape[0]
    g = np.arange(N)
    edges = [(int(a), int(N + b)) for s in sorted({int(x) for x in S}) for a, b in zip(g, MT[s])]
    return 2 * N, edges


# ------------------------------------------------------------------------------- candidates and fallback

def _candidates():
    """(kind, m, k, lam, order): groups of order >= 343, smallest first, Heisenberg(7) and Z_49 x| Z_7 first."""
    out = [("heis", 7, 0, 0, 343), ("meta", 49, 7, 8, 343)]
    for NN in range(344, 401):
        found = False
        for k in range(2, NN):
            if found or NN % k:
                continue
            m = NN // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 and lam != 1:
                    out.append(("meta", m, k, lam, NN))
                    found = True
                    break
    return out


def _make(c):
    if c[0] == "heis":
        return group_heis(c[1])
    return group_meta(c[1], c[2], c[3])


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    if D >= 1 and d >= 1:
        if D >= 2:
            return lib.haar_graph(d, range(d))
        return 2, [(0, 1)]
    return 1, []


def _fallback(d, D):
    """Valid order-660 Haar graph for d=6, D=5 (checked), else a trivial graph."""
    try:
        MT, _ = group_meta(33, 10, 26)
        n, edges = _graph(MT, [0, 179, 116, 180, 47, 306])
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
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    cands = _candidates()
    tables = {}
    best = None  # (n, edges)
    while time.monotonic() < deadline:
        best_group = best[0] // 2 if best else 0
        eligible = [i for i, c in enumerate(cands) if c[4] > best_group]
        if not eligible:
            break
        for idx in eligible:
            now = time.monotonic()
            if now >= deadline:
                break
            c = cands[idx]
            if c[4] <= (best[0] // 2 if best else 0):
                continue
            slice_end = min(deadline, now + (6.0 if idx < 2 else 2.0))
            try:
                if idx not in tables:
                    tables[idx] = _make(c)
                MT, inv = tables[idx]
                S = _anneal(MT, inv, slice_end, rng)
            except Exception:
                continue
            if S is not None:
                g = _graph(MT, S)
                if lib.is_valid(g[0], g[1], DEG, DIAM) and (best is None or g[0] > best[0]):
                    best = g
    if best is not None:
        return best
    return _fallback(d, D)
