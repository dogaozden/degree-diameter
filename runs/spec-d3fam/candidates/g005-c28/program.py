import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Helpers: adjacency matrices, bipartition, and a fast penalised cost.
# ----------------------------------------------------------------------------

def _bicolor(n, edges):
    """Two-colour a bipartite graph (vertices with no edges get colour 0)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return np.array(color, dtype=np.int64)


def _to_matrix(n, edges):
    A = np.zeros((n, n), dtype=np.float32)
    for u, v in edges:
        A[u, v] = 1.0
        A[v, u] = 1.0
    return A


def _set(A, i, j, v):
    A[i, j] = v
    A[j, i] = v


def _cost(A, d, D):
    """Bad pairs (distance > D) plus 4 * degree excess. Zero means valid for (d, D)."""
    n = A.shape[0]
    deg = A.sum(axis=1)
    excess = int(np.maximum(deg - d, 0).sum())
    M = A + np.eye(n, dtype=np.float32)
    R = M
    for _ in range(D - 1):
        R = ((R @ M) > 0).astype(np.float32)
    zeros = n * n - int(np.count_nonzero(R))  # diagonal is always nonzero
    return zeros // 2 + 4 * excess


# ----------------------------------------------------------------------------
# Simulated annealing over bipartite graphs of fixed vertex set.
# Moves: toggle a cross pair (biased toward deficient vertices), or a
# degree-preserving 2-switch. Cost = bad pairs + penalty for excess degree.
# ----------------------------------------------------------------------------

def _anneal(A, side, d, D, deadline, rng):
    sideA = [int(i) for i in np.flatnonzero(side == 0)]
    sideB = [int(i) for i in np.flatnonzero(side == 1)]
    cost = _cost(A, d, D)
    T0, T1 = 2.0, 0.15
    start = time.monotonic()
    span = max(1e-6, deadline - start)

    while True:
        if cost == 0:
            return A
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - start) / span
        T = T0 * (T1 / T0) ** frac

        if rng.random() < 0.5:
            deg = A.sum(axis=1)
            if rng.random() < 0.6:
                fa = [a for a in sideA if deg[a] < d]
                fb = [b for b in sideB if deg[b] < d]
            else:
                fa, fb = sideA, sideB
            if not fa or not fb:
                fa, fb = sideA, sideB
            a = rng.choice(fa)
            b = rng.choice(fb)
            old = A[a, b]
            _set(A, a, b, 1.0 - old)
            c2 = _cost(A, d, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                _set(A, a, b, old)
        else:
            a1 = rng.choice(sideA)
            a2 = rng.choice(sideA)
            nb1 = np.flatnonzero(A[a1])
            nb2 = np.flatnonzero(A[a2])
            if len(nb1) == 0 or len(nb2) == 0:
                continue
            b1 = int(nb1[rng.randrange(len(nb1))])
            b2 = int(nb2[rng.randrange(len(nb2))])
            if a1 == a2 or b1 == b2 or A[a1, b2] or A[a2, b1]:
                continue
            _set(A, a1, b1, 0.0)
            _set(A, a2, b2, 0.0)
            _set(A, a1, b2, 1.0)
            _set(A, a2, b1, 1.0)
            c2 = _cost(A, d, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                _set(A, a1, b2, 0.0)
                _set(A, a2, b1, 0.0)
                _set(A, a1, b1, 1.0)
                _set(A, a2, b2, 1.0)


def _grow(A, side, d, D, deadline, rng):
    """Repeatedly add one vertex per side and anneal back to a valid graph."""
    best = (A, side)
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.5:
            break
        A0, s0 = best
        n = A0.shape[0]
        A2 = np.zeros((n + 2, n + 2), dtype=np.float32)
        A2[:n, :n] = A0
        s2 = np.concatenate([s0, np.array([0, 1], dtype=s0.dtype)])
        attempt_end = min(deadline, now + max(1.5, 0.35 * remaining))
        res = _anneal(A2, s2, d, D, attempt_end, rng)
        if res is not None:
            best = (res, s2)
    return best


# ----------------------------------------------------------------------------
# Bases.
# ----------------------------------------------------------------------------

def _pg_largest(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _d3_base(d):
    """Best base for D = 3: optimal PG when d-1 is a prime power, else AL record, else PG."""
    if lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)
        except (ValueError, StopIteration, KeyError):
            pass
    return _pg_largest(d)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 4.0))

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    kdd = lib.haar_graph(d, range(d))
    if D == 2:
        return kdd
    best_n, best_e = kdd

    rng = random.Random(seed * 1000003 + d * 101 + D)

    if D == 3:
        base = _d3_base(d)
        if base is None:
            return kdd
        n0, e0 = base
        if not lib.is_valid(n0, e0, d, D):
            return kdd
        if lib.is_prime_power(d - 1):
            return base  # Moore-optimal; growth is impossible
    else:
        n0, e0 = kdd

    if n0 > best_n:
        best_n, best_e = n0, e0

    colors = _bicolor(n0, e0)
    A = _to_matrix(n0, e0)
    A_sol, _ = _grow(A, colors, d, D, deadline, rng)

    n = A_sol.shape[0]
    if n > best_n:
        edges = [(int(i), int(j)) for i, j in zip(*np.nonzero(np.triu(A_sol, 1)))]
        if lib.is_valid(n, edges, d, D):
            return n, edges

    if not lib.is_valid(best_n, best_e, d, D):
        return kdd
    return best_n, best_e
