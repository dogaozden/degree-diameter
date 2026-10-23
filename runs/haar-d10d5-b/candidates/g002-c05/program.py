"""Bi-Cayley (two-orbit) search for the bipartite degree-diameter problem at diameter 5.

THEORY.  Let G be a group of order N and b = 2 orbits per side.  Vertices are (g, A_i) and (g, B_j) for g in G,
i, j in {0, 1}, with edges (g, A_i) ~ (s*g, B_j) for s in S_ij, where each S_ij has k = d/2 elements.  Every
vertex has degree d, the graph is bipartite, and it has 4N vertices.  Right multiplication by any h in G is an
automorphism, so every pair of vertices can be moved to a pair with one endpoint at a base vertex (1, X).
Therefore the diameter is at most D iff a BFS from each of the four base vertices reaches everything within D steps.

This is a different search space from the Haar graphs (one orbit per side, one connection set).  The 2x2 array of
connection sets gives more freedom, and 4N > record can be reached with N about 1000 instead of about 2000.

SEARCH.  Simulated annealing over the four k-subsets, with a single-slot replacement per step.  The cost is the
number of (base vertex, target) pairs at distance more than D, computed with a vectorised bitset BFS in numpy.
A cost-0 result is rebuilt as an edge list and checked with lib.is_valid.  If nothing is found in budget, a
precomputed valid Haar graph (2 * 1791 = 3582 vertices) is returned.
"""
import itertools
import math
import time

import numpy as np

import lib


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
    """Table of a group given as an (N, c) integer coordinate array (element 0 must be the identity)
    and a vectorised product mulfun(X, Y) of two (..., c) arrays."""
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
    """Heisenberg group mod p, order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)  # (0,0,0) is first

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, order p(p^2-1)."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k (the maps t -> a*t + b with a of order dividing k).  Default k = q-1 gives AGL(1, q)."""
    F = lib.GF(q)
    k = q - 1 if k is None else k
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    assert len(H) == k
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
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def _root_of_unity(m, k):
    """Return x with x^k = 1 mod m and x of order exactly k (m prime, k | m-1)."""
    for x in range(2, m):
        if pow(x, k, m) == 1 and all(pow(x, e, m) != 1 for e in range(1, k) if k % e == 0):
            return x
    raise ValueError("no root of unity of the required order")


# ----------------------------------------------------------------------------------- bi-Cayley graph

def make_nbr(MT, inv, S):
    """Neighbour table (4N, d) of the two-orbit bi-Cayley graph.

    Vertex ids: A_i, element g -> i*N + g (i = 0, 1); B_j, element h -> (2 + j)*N + h.
    Edges: (g, A_i) ~ (s*g, B_j) for s in S[i, j].
    """
    N = MT.shape[0]
    b = S.shape[0]
    blocks = []
    for i in range(b):
        cols = [MT[S[i, j]].T.astype(np.int64) + (b + j) * N for j in range(b)]
        blocks.append(np.concatenate(cols, axis=1))
    for j in range(b):
        cols = [MT[inv[S[i, j]]].T.astype(np.int64) + i * N for i in range(b)]
        blocks.append(np.concatenate(cols, axis=1))
    return np.concatenate(blocks, axis=0)


def bfs_cost(nbr, N, D):
    """Number of (base vertex, vertex) pairs at distance more than D, base vertices = the four orbit identities."""
    n = nbr.shape[0]
    reach = np.zeros((n, 4), dtype=bool)
    src = np.array([0, N, 2 * N, 3 * N], dtype=np.int64)
    reach[src, np.arange(4)] = True
    for _ in range(D):
        reach = reach | reach[nbr].any(axis=1)
    return int(4 * n - reach.sum())


def anneal(MT, inv, d, deadline, rng, D=5, T=1.5, patience=2500):
    """Simulated annealing over the four k-subsets (k = d/2).  Returns (best S, best cost)."""
    N = MT.shape[0]
    b, k = 2, d // 2

    def rand_S():
        S = np.empty((b, b, k), dtype=np.int64)
        for i in range(b):
            for j in range(b):
                S[i, j] = rng.choice(N, k, replace=False)
        return S

    def cost_of(S):
        return bfs_cost(make_nbr(MT, inv, S), N, D)

    best, bestc = None, 10 ** 9
    S = rand_S()
    cur = cost_of(S)
    best, bestc = S.copy(), cur
    since = 0
    while time.monotonic() < deadline:
        if cur == 0:
            break
        i, j = int(rng.integers(b)), int(rng.integers(b))
        t = int(rng.integers(k))
        x = int(rng.integers(N))
        if x in S[i, j]:
            continue
        old = S[i, j, t]
        S[i, j, t] = x
        c = cost_of(S)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c
            if cur < bestc:
                best, bestc = S.copy(), cur
                since = 0
        else:
            S[i, j, t] = old
        since += 1
        if since > patience:
            S = rand_S()
            cur = cost_of(S)
            since = 0
    return best, bestc


def run_bicayley(d, D, seed, deadline_all):
    """Try several groups of order about 1000-1100 (so 4N is at least the record 4000); return (n, edges) or None."""
    rng = np.random.default_rng(seed)
    lam_m337 = _root_of_unity(337, 3)
    lam_m101 = _root_of_unity(101, 10)
    cands = [
        ("SL(2,7) x Z3, order 1008", lambda: group_times_cyclic(group_sl2(7), 3)),
        ("meta 337/3, order 1011", lambda: group_meta(337, 3, lam_m337)),
        ("Heis(7) x Z3, order 1029", lambda: group_times_cyclic(group_heis(7), 3)),
        ("meta 101/10, order 1010", lambda: group_meta(101, 10, lam_m101)),
        ("AGL(1,11) x Z10, order 1100", lambda: group_times_cyclic(group_agl(11), 10)),
    ]
    for idx, (_, builder) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline_all:
            break
        end = now + (deadline_all - now) / (len(cands) - idx)
        try:
            MT, inv = builder()
            S, c = anneal(MT, inv, d, end, rng, D)
        except Exception:
            continue
        if S is not None and c == 0:
            N = MT.shape[0]
            nbr = make_nbr(MT, inv, S)
            n = 4 * N
            edges = [(u, int(v)) for u in range(2 * N) for v in nbr[u]]
            try:
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                pass
    return None


# -------------------------------------------------------------------------------- fallback (Haar)

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


def fallback_haar(d, D):
    """Valid Haar graph of order 2 * 1791 = 3582, checked at run time."""
    try:
        MT, _ = group_meta(199, 9, 180)
        g = checked(MT, [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ======================================================================================== cell: d10D5

TARGET = (10, 5)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline_all = t0 + 0.75 * time_limit
    try:
        g = run_bicayley(d, D, seed, deadline_all)
        if g is not None:
            return g
    except Exception:
        pass
    return fallback_haar(d, D)
