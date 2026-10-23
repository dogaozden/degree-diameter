"""Bi-Cayley search for the d=6, D=5 target, with safe fallbacks.

Two orbits per side: vertices (g, A_i) and (g, B_j) for g in G, i, j in {0, 1}.
Edges (g, A_i) ~ (s*g, B_j) for s in S_ij. Block sizes are [[a, 6-a], [6-a, a]], so
every vertex has degree 6. Right multiplication by any h in G is an automorphism, so
the diameter is at most 5 iff the four sources (e, A_0), (e, A_1), (e, B_0), (e, B_1)
reach every vertex within 5 steps. Each cost evaluation is four numpy BFS runs.
Annealing runs over several non-abelian metacyclic groups of order 172..190 (4|G| >= 688 > 684).
Every result is checked with lib.is_valid. Fallbacks: a valid order-330 Haar graph (660 vertices),
then a small always-valid graph.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
SLICE = 3.0          # seconds of annealing per group
T0, T1 = 2.0, 0.2    # geometric temperature schedule within one slice
N_LO, N_HI = 172, 190


def _safe_small(d, D):
    """Small graph that is valid for (d, D), checked with lib.is_valid."""
    cands = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        cands.append(lib.projective_plane_incidence(d - 1))
    if d >= 1 and D >= 2:
        cands.append((2 * d, [(i, d + j) for i in range(d) for j in range(d)]))
    if d >= 1 and D >= 1:
        cands.append((2, [(0, 1)]))
    for n, e in cands:
        try:
            if lib.is_valid(n, e, d, D):
                return n, e
        except Exception:
            pass
    return 1, []


def _candidates(lo, hi):
    """Non-abelian metacyclic groups Z_m x| Z_k of order N in [lo, hi], as (m, k, r), ordered by N."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for r in range(2, m):
                if r % m == 1 or math.gcd(r, m) != 1 or pow(r, k, m) != 1:
                    continue
                out.append((m, k, r))
    return out


def _group(m, k, r):
    """Return (N, M, iv): order, product table M[x, y] = x*y, and inverse array."""
    N, mul, inv = lib.semidirect_group(m, k, r)
    M = np.array([[mul(x, y) for y in range(N)] for x in range(N)], dtype=np.int64)
    iv = np.array([inv(x) for x in range(N)], dtype=np.int64)
    return N, M, iv


def _nbr(N, M, iv, S):
    """Neighbour table (4N, 6). A_i vertex g is i*N+g; B_j vertex h is 2N+j*N+h."""
    g = np.arange(N, dtype=np.int64)
    nbr = np.empty((4 * N, 6), dtype=np.int64)
    for i in range(2):
        cols = [2 * N + j * N + M[s, g] for j in range(2) for s in S[i][j]]
        nbr[i * N:(i + 1) * N] = np.stack(cols, axis=1)
    for j in range(2):
        cols = [i * N + M[iv[s], g] for i in range(2) for s in S[i][j]]
        nbr[2 * N + j * N: 2 * N + (j + 1) * N] = np.stack(cols, axis=1)
    return nbr


def _cost(nbr, N, D):
    """Total number of (source, vertex) pairs at distance > D from the four orbit representatives."""
    n = nbr.shape[0]
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            nxt = nbr[front].ravel()
            nxt = np.unique(nxt[~seen[nxt]])
            if nxt.size == 0:
                break
            seen[nxt] = True
            front = nxt
        total += n - int(seen.sum())
    return total


def _edges(nbr):
    """Edge list from the neighbour table; A rows are 0..2N-1."""
    h = nbr.shape[0] // 2
    return nbr.shape[0], [(u, int(v)) for u in range(h) for v in nbr[u]]


def _anneal(N, M, iv, rng, end, D):
    """One annealing run over block sets until cost 0 or the deadline. Returns S or None."""
    a = int(rng.integers(2, 5))  # 2, 3 or 4
    sizes = ((a, 6 - a), (6 - a, a))
    S = [[[int(x) for x in rng.choice(N, sizes[i][j], replace=False)] for j in range(2)] for i in range(2)]
    cur = _cost(_nbr(N, M, iv, S), N, D)
    start = time.monotonic()
    span = max(end - start, 1e-6)
    while cur > 0:
        now = time.monotonic()
        if now >= end:
            break
        frac = (now - start) / span
        T = T0 * (T1 / T0) ** frac
        i, j = int(rng.integers(2)), int(rng.integers(2))
        blk = S[i][j]
        p = int(rng.integers(len(blk)))
        old = blk[p]
        x = int(rng.integers(N))
        while x in blk:
            x = int(rng.integers(N))
        blk[p] = x
        new = _cost(_nbr(N, M, iv, S), N, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
            cur = new
        else:
            blk[p] = old
    return S if cur == 0 else None


def _search(D, rng, deadline):
    """Cycle through candidate groups, annealing in short slices. Returns (n, edges) checked, or None."""
    cands = _candidates(N_LO, N_HI)
    if not cands:
        return None
    idx = 0
    while time.monotonic() < deadline - 0.5:
        now = time.monotonic()
        m, k, r = cands[idx % len(cands)]
        idx += 1
        N, M, iv = _group(m, k, r)
        end = min(deadline, now + SLICE)
        S = _anneal(N, M, iv, rng, end, D)
        if S is not None:
            n, edges = _edges(_nbr(N, M, iv, S))
            if lib.is_valid(n, edges, 6, D):
                return n, edges
    return None


def _haar_fallback():
    """Valid order-330 Haar graph (660 vertices) for d=6, D=5."""
    N, mul, _ = lib.semidirect_group(33, 10, 26)
    S = [0, 179, 116, 180, 47, 306]
    return 2 * N, [(g, N + mul(s, g)) for s in S for g in range(N)]


def _build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return _safe_small(d, D)
    t0 = time.monotonic()
    budget = max(1.0, min(0.80 * time_limit, time_limit - 6.0))
    rng = np.random.default_rng(seed)
    try:
        res = _search(D, rng, t0 + 0.85 * budget)
        if res is not None:
            return res
    except Exception:
        pass
    try:
        n, edges = _haar_fallback()
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return _safe_small(d, D)


def build(d, D, seed, time_limit):
    try:
        return _build(d, D, seed, time_limit)
    except Exception:
        return _safe_small(d, D)
