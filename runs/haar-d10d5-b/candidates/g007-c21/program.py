"""Two-orbit bi-Cayley search for the d=10, D=5 target, with a validated Haar fallback.

THEORY.  Let G be a group of order N.  Vertices are A_0(g), A_1(g), B_0(g), B_1(g) for g in G, so 4N vertices.
Edges are A_i(g) ~ B_j(s*g) for s in S_ij.  With |S_00| = |S_11| = a and |S_01| = |S_10| = d - a, every vertex has
degree d.  Right multiplication by h in G is an automorphism that fixes each orbit, so every vertex is equivalent to
one of the four identity vertices.  Diameter <= 5 therefore holds iff BFS (depth 5) from those four sources reaches
everything.  The cost is the number of unreached (source, target) pairs, summed over the four sources.  Cost 0 means
the graph is valid.

This differs from the parent's Haar search: it has two orbits per side, so it has 4N vertices instead of 2N, and it
searches S_ij directly with single-element moves and Metropolis acceptance.  The group is chosen so that 4N > 4000.

SAFETY.  A valid Haar fallback (order 1791, 3582 vertices) is built and checked first.  A bi-Cayley result is returned
only after lib.is_valid accepts it.  Any exception or timeout returns the fallback.  Other (d, D) cases return the
small trivial graph.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
BLOCKS = [(0, 0), (0, 1), (1, 0), (1, 1)]


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
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi, None]] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def meta_groups(lo, hi):
    """(m, k, lam) with m*k = N in [lo, hi], lam != 1, lam^k = 1 mod m, gcd(lam, m) = 1.  Ordered by N."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    out.append((m, k, lam))
                    break
    return out


# ------------------------------------------------------------------------------------ Haar fallback

def haar_edges(MT, S):
    """Haar graph edges: A-vertex g is g, B-vertex g is N + g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    g = list(range(N))
    edges = []
    for s in sorted({int(x) for x in S}):
        for a, b in zip(g, MT[s].tolist()):
            edges.append((a, N + b))
    return 2 * N, edges


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def haar_fallback(d, D):
    """Valid Haar graph of order 3582 for (10, 5), checked with lib.is_valid; otherwise trivial."""
    try:
        MT, _ = group_meta(199, 9, 180)
        n, edges = haar_edges(MT, [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


# --------------------------------------------------------------------------- bi-Cayley graph and cost

def bicayley_edges(MT, blocks):
    """Directed-source/target arrays of the bi-Cayley graph.  A_i(g) = i*N + g, B_j(g) = 2N + j*N + g."""
    N = MT.shape[0]
    ar = np.arange(N, dtype=np.int64)
    src_parts, dst_parts = [], []
    for (i, j), S in zip(BLOCKS, blocks):
        s_arr = np.asarray(S, dtype=np.int64)
        src = i * N + np.tile(ar, len(s_arr))
        dst = 2 * N + j * N + MT[s_arr].astype(np.int64).ravel()
        src_parts.append(src)
        dst_parts.append(dst)
    return np.concatenate(src_parts), np.concatenate(dst_parts)


def cost(MT, blocks):
    """Unreached (source, target) pairs within depth 5, over the four identity sources.  Zero means diameter <= 5."""
    N = MT.shape[0]
    n = 4 * N
    src, dst = bicayley_edges(MT, blocks)
    U = np.concatenate([src, dst])
    V = np.concatenate([dst, src])
    total = 0
    for s0 in (0, N, 2 * N, 3 * N):
        reached = np.zeros(n, dtype=bool)
        reached[s0] = True
        frontier = reached.copy()
        for _ in range(5):
            hit = np.zeros(n, dtype=bool)
            hit[V[frontier[U]]] = True
            hit &= ~reached
            if not hit.any():
                break
            reached |= hit
            frontier = hit
        total += n - int(reached.sum())
    return total


def bicayley_graph(MT, blocks):
    """Return (n, edges) of the bi-Cayley graph as Python int pairs."""
    N = MT.shape[0]
    src, dst = bicayley_edges(MT, blocks)
    return 4 * N, list(zip(src.tolist(), dst.tolist()))


# ------------------------------------------------------------------------------------------ search

def anneal(MT, sizes, deadline, rng, temp=2.0, patience=1500):
    """Single-element Metropolis moves on the four connection sets, with restarts when stuck.
    Returns (best blocks, best cost)."""
    N = MT.shape[0]

    def fresh():
        return [rng.choice(N, size=s, replace=False).astype(np.int64) for s in sizes]

    blocks = fresh()
    cur = cost(MT, blocks)
    best = cur
    bestB = [b.copy() for b in blocks]
    since = 0
    while cur > 0 and time.monotonic() < deadline:
        if since > patience:
            blocks = fresh()
            cur = cost(MT, blocks)
            since = 0
            if cur < best:
                best = cur
                bestB = [b.copy() for b in blocks]
            continue
        b = int(rng.integers(4))
        t = int(rng.integers(len(blocks[b])))
        x = int(rng.integers(N))
        if np.any(blocks[b] == x):
            since += 1
            continue
        old = blocks[b][t]
        blocks[b][t] = x
        c = cost(MT, blocks)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = c
            if cur < best:
                best = cur
                bestB = [bb.copy() for bb in blocks]
                since = 0
            else:
                since += 1
        else:
            blocks[b][t] = old
            since += 1
    return bestB, best


# ------------------------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget_end = t0 + 0.78 * time_limit
    fb = haar_fallback(d, D)
    try:
        rng = np.random.default_rng(seed)
        groups = meta_groups(1001, 1040)[:4]
        if not groups:
            return fb
        a = d // 2
        sizes = [a, d - a, d - a, a]
        for idx, (m, k, lam) in enumerate(groups):
            now = time.monotonic()
            if now >= budget_end:
                break
            share = (budget_end - now) / (len(groups) - idx)
            try:
                MT, _ = group_meta(m, k, lam)
            except Exception:
                continue
            blocks, c = anneal(MT, sizes, now + share, rng)
            if c == 0:
                n, edges = bicayley_graph(MT, blocks)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
    except Exception:
        pass
    return fb
