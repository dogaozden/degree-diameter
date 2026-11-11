"""Bold variant for the d=10, D=5 target: a random-regular bipartite search instead of Haar graphs.

Idea: a bipartite d-regular graph with m vertices per side has 2m vertices. Random d-regular bipartite
graphs have diameter close to 5 at this size, so the number of ordered pairs at distance > 5 can be driven
to zero by simulated annealing over double-edge swaps, which keep the graph bipartite and d-regular.
Each cost evaluation is a packed-bit BFS in numpy. Every result is checked with lib.is_valid.
If the search fails, the parent's valid Haar graph (order 1791, 3582 vertices) is returned. Other cases
return the trivial graph. Every path ends in a checked graph or a trivial valid one.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
POP = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


# ----------------------------------------------------------------- fallback constructions

def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j. Needs lam^k = 1 mod m."""
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


def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


# ----------------------------------------------------------------- random-regular search

def _ball_cost(adj, n, d, D):
    """Number of ordered pairs (u, v), u != v, at distance > D. Packed-bit BFS over all vertices."""
    W = (n + 7) // 8
    idx = np.arange(n)
    reach = np.zeros((n, W), dtype=np.uint8)
    reach[idx, idx >> 3] = np.left_shift(1, idx & 7).astype(np.uint8)
    for _ in range(D):
        new = reach.copy()
        for k in range(d):
            new |= reach[adj[:, k]]
        reach = new
    return n * n - int(POP[reach].sum())


def _rep(row, old, new):
    row[np.flatnonzero(row == old)[0]] = new


def _do_swap(adj, m, a1, b1, a2, b2):
    """Edges (a1,b1),(a2,b2) become (a1,b2),(a2,b1). Vertices: A-side a, B-side m+b."""
    _rep(adj[a1], m + b1, m + b2)
    _rep(adj[a2], m + b2, m + b1)
    _rep(adj[m + b1], a1, a2)
    _rep(adj[m + b2], a2, a1)


def _search_regular(m, d, D, deadline, rng):
    """Anneal a d-regular bipartite graph on m+m vertices toward diameter <= D. Returns edges or None."""
    n = 2 * m
    ar = np.arange(m)
    sh = np.arange(d)
    eA = np.repeat(ar, d).astype(np.int64)
    eB = ((ar[:, None] + sh[None, :]) % m).ravel().astype(np.int64)
    adj = np.empty((n, d), dtype=np.int64)
    adj[:m] = m + (ar[:, None] + sh[None, :]) % m
    adj[m:] = (ar[:, None] - sh[None, :]) % m
    present = set((eA * m + eB).tolist())
    M = len(eA)

    def try_move(i, j):
        a1, b1 = int(eA[i]), int(eB[i])
        a2, b2 = int(eA[j]), int(eB[j])
        if a1 == a2 or b1 == b2:
            return None
        if a1 * m + b2 in present or a2 * m + b1 in present:
            return None
        return a1, b1, a2, b2

    # Mix the circulant start with unevaluated double-edge swaps.
    for _ in range(6 * M):
        i, j = int(rng.integers(M)), int(rng.integers(M))
        mv = try_move(i, j)
        if mv is None:
            continue
        a1, b1, a2, b2 = mv
        _do_swap(adj, m, a1, b1, a2, b2)
        present.discard(a1 * m + b1)
        present.discard(a2 * m + b2)
        present.add(a1 * m + b2)
        present.add(a2 * m + b1)
        eB[i] = b2
        eB[j] = b1

    cur = _ball_cost(adj, n, d, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 2.0 * (1.0 - (now - t0) / span) + 0.3
        i, j = int(rng.integers(M)), int(rng.integers(M))
        mv = try_move(i, j)
        if mv is None:
            continue
        a1, b1, a2, b2 = mv
        _do_swap(adj, m, a1, b1, a2, b2)
        new = _ball_cost(adj, n, d, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            present.discard(a1 * m + b1)
            present.discard(a2 * m + b2)
            present.add(a1 * m + b2)
            present.add(a2 * m + b1)
            eB[i] = b2
            eB[j] = b1
            cur = new
        else:
            _do_swap(adj, m, a1, b2, a2, b1)  # undo

    if cur != 0:
        return None
    return [(int(a), int(m + b)) for a, b in zip(eA, eB)]


# ----------------------------------------------------------------- target dispatch

def _target(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.6 * time_limit
    rng = np.random.default_rng(seed)
    m = 2001  # 4002 vertices, which beats the 4000 record if it validates
    try:
        edges = _search_regular(m, d, D, deadline, rng)
        if edges is not None and lib.is_valid(2 * m, edges, d, D):
            return 2 * m, edges
    except Exception:
        pass
    # Safe fallback: the parent's valid Haar graph (order 1791 per side, 3582 vertices).
    try:
        MT, _ = group_meta(199, 9, 180)
        n, edges = haar_edges(MT, [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return None


def build(d, D, seed, time_limit):
    try:
        if (d, D) == TARGET:
            res = _target(d, D, seed, time_limit)
            if res is not None:
                return res
    except Exception:
        pass
    try:
        return trivial(d, D)
    except Exception:
        return 1, []
