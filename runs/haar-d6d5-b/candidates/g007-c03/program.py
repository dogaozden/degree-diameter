"""Bi-Cayley two-orbit lifts for the bipartite degree-diameter problem, d = 6, D = 5 (numpy only).

CONSTRUCTION.  Take a finite group G (order N) and four connection blocks S[i][j] (i, j in {0, 1}), with
|S[i][j]| = sz[i][j] and row and column sums equal to 6.  Vertices are A_i(x) and B_j(y) for x, y in G, so there
are 4N vertices.  Edges are A_i(x) ~ B_j(s*x) for every s in S[i][j].  Every vertex has degree 6 and the graph is
bipartite.  Right multiplication by any h in G is an automorphism, so the diameter is at most 5 iff the four
representatives A_0(e), A_1(e), B_0(e), B_1(e) reach every vertex within 5 steps.  This gives an exact, cheap cost:
the number of (representative, vertex) pairs at distance > 5.  The search anneals the block elements to cost 0.

This family has more freedom than a single Haar graph (two A-orbits and two B-orbits instead of one).  It targets
2N > 342 with N in the window 172 to 260 (4N >= 688 beats the record 684).  Metacyclic groups Z_m x| Z_k and cyclic
groups are tried from the smallest order upward.  Every candidate is verified with lib.is_valid.  If nothing is
found, a precomputed valid Haar graph of order 660 is returned.  Other (d, D) cases get a small always-valid graph.
"""
import math
import time

import numpy as np

import lib


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


def group_candidates(lo, hi):
    """(order, m, k, lam) for groups of order in [lo, hi]: cyclic groups, and metacyclic Z_m x| Z_k with lam != 1."""
    out = []
    for k in range(1, 9):
        for m in range(2, hi // k + 1):
            N = m * k
            if N < lo or N > hi:
                continue
            if k == 1:
                out.append((N, m, 1, 1))
                continue
            lams = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            for r in lams[:2]:
                out.append((N, m, k, r))
    out.sort(key=lambda t: (t[0], t[2]))
    return out


# --------------------------------------------------------------------------------- bi-Cayley model

def build_adj(MT, inv, blocks, G):
    """Adjacency (4G x 6) of the bi-Cayley graph.  A_i(x) = i*G + x, B_j(y) = 2G + j*G + y."""
    n = 4 * G
    adj = np.zeros((n, 6), dtype=np.int64)
    xs = np.arange(G)
    for i in range(2):
        c = 0
        for j in range(2):
            for s in blocks[i][j]:
                adj[i * G + xs, c] = 2 * G + j * G + MT[s, xs]
                c += 1
    for j in range(2):
        c = 0
        for i in range(2):
            for s in blocks[i][j]:
                adj[2 * G + j * G + xs, c] = i * G + MT[inv[s], xs]
                c += 1
    return adj


def bfs_cost(adj, n, G):
    """Number of (representative, vertex) pairs at distance > 5, over the four representatives."""
    total = 0
    for src in (0, G, 2 * G, 3 * G):
        vis = np.zeros(n, dtype=bool)
        vis[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(5):
            nb = np.unique(adj[front].ravel())
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            vis[nb] = True
            front = nb
        total += n - int(vis.sum())
    return total


def _cost(MT, inv, blocks):
    G = MT.shape[0]
    return bfs_cost(build_adj(MT, inv, blocks, G), 4 * G, G)


def _copy_blocks(blocks):
    return [[list(b) for b in row] for row in blocks]


def anneal(MT, inv, sz, rng, deadline, T=0.8, patience=2000):
    """Anneal the block elements toward cost 0.  Returns (best cost, best blocks)."""
    G = MT.shape[0]
    blocks = [[rng.choice(G, sz[i][j], replace=False).tolist() for j in range(2)] for i in range(2)]
    cur = _cost(MT, inv, blocks)
    best, bestb = cur, _copy_blocks(blocks)
    since = 0
    while best > 0 and since < patience and time.monotonic() < deadline:
        i = int(rng.integers(2))
        j = int(rng.integers(2))
        blk = blocks[i][j]
        k = int(rng.integers(len(blk)))
        g = int(rng.integers(G))
        if g in blk:
            continue
        old = blk[k]
        blk[k] = g
        c = _cost(MT, inv, blocks)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c
            if c < best:
                best, bestb, since = c, _copy_blocks(blocks), 0
        else:
            blk[k] = old
        since += 1
    return best, bestb


def graph_from(MT, inv, blocks):
    """The checked bi-Cayley graph for these blocks, or None if lib.is_valid rejects it."""
    G = MT.shape[0]
    adj = build_adj(MT, inv, blocks, G)
    edges = [(a, int(b)) for a in range(2 * G) for b in adj[a]]
    n = 4 * G
    return (n, edges) if lib.is_valid(n, edges, 6, 5) else None


# --------------------------------------------------------------------- Haar fallback (valid, 660)

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


def fallback(d, D):
    try:
        MT, _ = group_meta(33, 10, 26)
        g = checked(MT, [0, 179, 116, 180, 47, 306], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ----------------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != (6, 5):
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + max(0.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = np.random.default_rng(seed)
    best_graph, best_order = None, 171
    cands = group_candidates(172, 260)
    while time.monotonic() < deadline:
        todo = [c for c in cands if c[0] > best_order]
        if not todo:
            break
        for N, m, k, lam in todo:
            if time.monotonic() >= deadline:
                break
            if N <= best_order:
                continue
            try:
                MT, inv = group_meta(m, k, lam)
            except Exception:
                continue
            slice_end = min(deadline, time.monotonic() + 2.5)
            while time.monotonic() < slice_end and N > best_order:
                a = int(rng.integers(1, 4))
                sz = [[a, 6 - a], [6 - a, a]]
                c, blocks = anneal(MT, inv, sz, rng, slice_end)
                if c == 0:
                    try:
                        g = graph_from(MT, inv, blocks)
                    except Exception:
                        g = None
                    if g is not None:
                        best_graph, best_order = g, N
    if best_graph is not None:
        return best_graph
    return fallback(d, D)
