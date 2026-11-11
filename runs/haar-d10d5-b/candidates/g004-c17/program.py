"""Two-orbit bipartite lifts for the bipartite degree-diameter problem (d=10, D=5), with a Haar-graph fallback.

THEORY.  Let G be a group of order N (metacyclic Z_m x| Z_k).  Take base vertices A_0, A_1, B_0, B_1 and
connection sets S_ij, each of size K_PER = 5.  The lift has vertices (A_i, g) and (B_j, g) for g in G, with
edges (A_i, g) ~ (B_j, s*g) for s in S_ij.  It is bipartite, 10-regular, and has 4N vertices.  Right
multiplication by any h in G is an automorphism, so the ball around (A_i, e) and (B_j, e) for the four base
vertices determines the diameter.  The lift has diameter <= 5 iff BFS from those four sources reaches every
vertex within 5 steps.  The cost is the total number of unreached (source, vertex) pairs; 0 means valid.

WHAT THIS FILE DOES.  For group orders N in 1001..1040 (giving 4004..4160 vertices, above the record 4000)
and then 960..1000, it anneals the four sets S_ij with numpy BFS cost evaluation and restarts across groups.
Any cost-0 lift is checked with lib.is_valid before it is returned.  If nothing is found in the budget, a
checked valid Haar graph (3582 vertices) is returned, and any other case gets a small always-valid graph.
"""
import math
import time

import numpy as np

import lib


TARGET = (10, 5)
K_PER = 5          # darts per (A_i, B_j) pair; each vertex then has degree 2*K_PER = 10


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def group_candidates(N, rng):
    """Nonabelian metacyclic (m, k, lam) with m*k = N, m >= 3, k >= 2, lam^k = 1 mod m, lam != 1."""
    out = []
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        lams = [l for l in range(2, m) if math.gcd(l, m) == 1 and pow(l, k, m) == 1 % m]
        if not lams:
            continue
        pick = rng.permutation(len(lams))[:2]
        out += [(m, k, lams[int(p)]) for p in pick]
    return out


# ------------------------------------------------------------------------------- two-orbit lift search

def lift_nbr(MT, inv, S):
    """Neighbour array (4N, 2*K_PER) of the lift.  A_i vertex g is i*N+g; B_j vertex h is 2N+j*N+h."""
    N = MT.shape[0]
    g = np.arange(N, dtype=np.int64)
    nbr = np.empty((4 * N, 2 * K_PER), dtype=np.int64)
    for i in range(2):
        cols = [2 * N + j * N + MT[s, g].astype(np.int64) for j in range(2) for s in S[i][j]]
        nbr[i * N:(i + 1) * N] = np.stack(cols, axis=1)
    for j in range(2):
        cols = [i * N + MT[inv[s], g].astype(np.int64) for i in range(2) for s in S[i][j]]
        nbr[2 * N + j * N:2 * N + (j + 1) * N] = np.stack(cols, axis=1)
    return nbr


def lift_cost(nbr, N):
    """Number of (source, vertex) pairs not reached within 5 steps; sources are the identity of each base vertex."""
    n = nbr.shape[0]
    srcs = [0, N, 2 * N, 3 * N]
    reach = np.zeros((4, n), dtype=bool)
    reach[np.arange(4), srcs] = True
    for _ in range(5):
        reach = reach | reach[:, nbr].any(axis=2)
    return 4 * n - int(reach.sum())


def _copy(S):
    return [[a.copy() for a in row] for row in S]


def _random_sets(N, rng):
    return [[rng.choice(N, K_PER, replace=False).astype(np.int64) for _ in range(2)] for _ in range(2)]


def anneal(MT, inv, N, rng, t_end, patience=3000, temp=2.0):
    """Single-slot Metropolis search on the four sets, with restarts.  Returns (best S, best cost)."""
    S = _random_sets(N, rng)
    cur = lift_cost(lift_nbr(MT, inv, S), N)
    best, bestS = cur, _copy(S)
    since = 0
    while cur > 0 and time.monotonic() < t_end:
        i = int(rng.integers(2))
        j = int(rng.integers(2))
        slot = int(rng.integers(K_PER))
        cand = int(rng.integers(N))
        if np.any(S[i][j] == cand):
            continue
        old = S[i][j][slot]
        S[i][j][slot] = cand
        c = lift_cost(lift_nbr(MT, inv, S), N)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = c
            if cur < best:
                best, bestS, since = cur, _copy(S), 0
        else:
            S[i][j][slot] = old
        since += 1
        if since > patience and cur > 0:
            S = _random_sets(N, rng)
            cur = lift_cost(lift_nbr(MT, inv, S), N)
            since = 0
    return bestS, best


def lift_edges(nbr, N):
    """Edges of the lift; each A-B edge is listed once, from its A endpoint."""
    return 4 * N, [(u, v) for u in range(2 * N) for v in nbr[u].tolist()]


# --------------------------------------------------------------------------------------- Haar fallback

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def fallback_graph(d, D):
    """Valid smaller Haar graph (3582 vertices at d=10, D=5), checked; otherwise the trivial graph."""
    try:
        MT, _ = FALLBACK[0]()
        n, edges = haar_edges(MT, FALLBACK[1])
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


# ------------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        t0 = time.monotonic()
        end = t0 + 0.72 * time_limit
        rng = np.random.default_rng(seed)

        # Phase 1: orders that beat the record (n = 4N > 4000).  Phase 2: slightly smaller orders.
        entries = []
        for N in list(range(1001, 1041)) + list(range(960, 1001)):
            for m, k, lam in group_candidates(N, rng):
                entries.append((N, m, k, lam))

        idx = 0
        slice_len = 4.0
        while entries and time.monotonic() < end - 1.0:
            N, m, k, lam = entries[idx % len(entries)]
            idx += 1
            MT, inv = group_meta(m, k, lam)
            slice_end = min(end, time.monotonic() + slice_len)
            S, c = anneal(MT, inv, N, rng, slice_end)
            if c == 0:
                nbr = lift_nbr(MT, inv, S)
                n, edges = lift_edges(nbr, N)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
    except Exception:
        pass
    return fallback_graph(d, D)
