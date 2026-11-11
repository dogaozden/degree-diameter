"""Haar-graph diameter-5 search with an incremental covering annealer (d=10, D=5).

NEW IDEA.  For a finite group G and a d-subset S of G, the Haar graph with vertices (g, A), (g, B)
and edges (g, A) ~ (s*g, B) is d-regular, bipartite, and has 2|G| vertices. Its diameter is at most 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G. So the search is over S, with cost = number of elements of G missed by
those two squared product sets. Each cost evaluation is a few gathers from the group multiplication table
(about 10^4 lookups), so the annealer runs thousands of steps per second.

The parent searched multi-orbit voltage lifts. This program instead anneals S over metacyclic groups
Z_m x|_r Z_k of order N just above the current best N, where the graph order is 2N. Any zero-cost S is
rebuilt as an explicit graph and checked with lib.is_valid before it is accepted. The valid Haar graph
(N = 1791) from the parent is kept as the fallback.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def small(d, D):
    """Always-valid small graph for calibration and other cases."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e
    if D >= 2 and d >= 1:
        return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]
    return 2, [(0, 1)]


# ------------------------------------------------------------------ groups

def group_table(m, k, r):
    """Z_m x|_r Z_k, element (a, j) -> a*k + j, with (a, j)(b, l) = (a + r^j b, j + l).

    Returns (MT, inv) where MT[x, y] is the product x*y and inv[x] is the inverse of x.
    """
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    ak = idx // k
    jk = idx % k
    MT = np.empty((N, N), dtype=np.int32)
    step = 256
    for lo in range(0, N, step):
        hi = min(N, lo + step)
        a = ak[lo:hi, None]
        j = jk[lo:hi, None]
        MT[lo:hi] = ((a + pw[j] * ak[None, :]) % m) * k + (j + jk[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def metacyclic_options(N):
    """All non-abelian metacyclic groups (m, k, r) with m*k = N, r != 1 mod m, r^k = 1 mod m."""
    opts = []
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


# ------------------------------------------------------------------ cost

def covering_cost(MT, inv, S, N):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2 in G. Zero iff the Haar graph has diameter <= 5."""
    Si = inv[S]
    A = MT[Si[:, None], S[None, :]].ravel()   # S^-1 S
    B = MT[S[:, None], Si[None, :]].ravel()   # S S^-1
    cost = 0
    for X in (A, B):
        P = MT[X[:, None], X[None, :]].ravel()
        mask = np.zeros(N, dtype=bool)
        mask[P] = True
        cost += N - int(np.count_nonzero(mask))
    return cost


def anneal(MT, inv, N, d, rng, deadline, L=3000):
    """Anneal a d-subset S with zero covering cost. Returns S, or None at the deadline."""
    while time.monotonic() < deadline:
        S = rng.choice(N, d, replace=False).astype(np.int64)
        cur = covering_cost(MT, inv, S, N)
        for step in range(L):
            if cur == 0:
                return S
            if (step & 63) == 0 and time.monotonic() >= deadline:
                return None
            T = 0.2 ** (step / L)            # geometric cooling from 1.0 to 0.2
            i = int(rng.integers(d))
            g = int(rng.integers(N))
            if np.any(S == g):
                continue
            old = S[i]
            S[i] = g
            c = covering_cost(MT, inv, S, N)
            if c <= cur or rng.random() < math.exp(-(c - cur) / T):
                cur = c
            else:
                S[i] = old
        if cur == 0:
            return S
    return None


# ------------------------------------------------------------------ graph

def haar_edges(MT, S, N):
    """Haar graph: A-vertex g is g, B-vertex g is N + g, edges (x, N + s*x) for s in S."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in S.tolist():
        col = MT[s].astype(np.int64)
        edges.extend(zip(ar.tolist(), (N + col).tolist()))
    return 2 * N, edges


# ------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return small(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        n, e = haar_edges(MT, np.array(FALLBACK_S, dtype=np.int64), m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    try:
        slice_len = max(3.0, 0.15 * budget)
        while time.monotonic() < deadline:
            best_N = best_n // 2
            N = best_N + 1 + int(rng.integers(0, 24))
            opts = metacyclic_options(N)
            if not opts:
                continue
            m, k, r = opts[int(rng.integers(len(opts)))]
            MT, inv = group_table(m, k, r)
            task_deadline = min(deadline, time.monotonic() + slice_len)
            S = anneal(MT, inv, N, d, rng, task_deadline)
            if S is None:
                continue
            n, e = haar_edges(MT, S, N)
            try:
                ok = n > best_n and lib.is_valid(n, e, d, D)
            except Exception:
                ok = False
            if ok:
                best_n, best_edges = n, e
    except Exception:
        pass

    if best_edges is None:
        return small(d, D)
    return best_n, best_edges
