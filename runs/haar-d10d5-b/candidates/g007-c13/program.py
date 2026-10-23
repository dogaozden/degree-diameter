"""Haar-graph search with a word-counting cover cost on metacyclic groups (d=10, D=5).

NEW HELPER.  A Haar graph of G with connection set S (|S| = d) has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G.  `cover_cost` counts the uncovered elements of both
sets with a few numpy table lookups, so each annealing step costs well under a millisecond.
Annealing then searches S directly, one slot at a time, and restarts on fresh metacyclic
groups of order just above the current best half-order.

Every zero-cost candidate is still checked with lib.is_valid before it is accepted.
A valid fallback Haar graph (3582 vertices) is kept, so the output is never worse than it.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
D_SIZE = 10
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l).  Returns (MT, inv)."""
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    ak = idx // k
    jk = idx % k
    MT = np.empty((N, N), dtype=np.int32)
    step = 128
    for lo in range(0, N, step):
        hi = min(N, lo + step)
        a = ak[lo:hi, None]
        j = jk[lo:hi, None]
        MT[lo:hi] = ((a + pw[j] * ak[None, :]) % m) * k + (j + jk[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def metacyclic_options(N):
    """All non-abelian metacyclic Z_m x|_r Z_k of order N, as (m, k, r) with r > 1."""
    opts = []
    for m in range(2, N + 1):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def cover_cost(MT, inv, S, N):
    """NEW HELPER: number of group elements missed by (S^-1 S)^2 and by (S S^-1)^2.

    The Haar graph of S has diameter <= 5 iff this cost is 0.
    """
    Sa = np.asarray(S, dtype=np.int64)
    Si = inv[Sa]
    T = np.unique(MT[Si[:, None], Sa[None, :]])        # s^-1 t
    T2 = np.unique(MT[T[:, None], T[None, :]])
    U = np.unique(MT[Sa[:, None], Si[None, :]])        # s t^-1
    U2 = np.unique(MT[U[:, None], U[None, :]])
    return 2 * N - len(T2) - len(U2)


def haar_from(MT, S, N):
    """Haar graph: (g, A) ~ (s*g, B), vertices A = g, B = N + g."""
    edges = []
    for s in sorted(set(S)):
        row = (N + MT[s].astype(np.int64)).tolist()
        edges.extend(zip(range(N), row))
    return 2 * N, edges


def anneal_group(MT, inv, N, steps, rng, deadline):
    """Anneal a size-D_SIZE set S with cover_cost; return a zero-cost S or None."""
    S = [int(x) for x in rng.choice(N, D_SIZE, replace=False)]
    cur = cover_cost(MT, inv, S, N)
    for step in range(steps):
        if cur == 0:
            return S
        if (step & 63) == 0 and time.monotonic() >= deadline:
            break
        i = int(rng.integers(D_SIZE))
        g = int(rng.integers(N))
        if g in S:
            continue
        old = S[i]
        S[i] = g
        c = cover_cost(MT, inv, S, N)
        temp = 0.05 + 1.5 * (1.0 - step / steps)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            S[i] = old
    return list(S) if cur == 0 else None


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.80 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        n, e = haar_from(MT, FALLBACK_S, m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    while time.monotonic() < deadline:
        half = best_n // 2
        N = half + 1 + int(rng.integers(0, 120))
        opts = metacyclic_options(N)
        if not opts:
            continue
        m, k, r = opts[int(rng.integers(len(opts)))]
        try:
            MT, inv = group_table(m, k, r)
        except Exception:
            continue
        NN = m * k
        S = anneal_group(MT, inv, NN, 8000, rng, deadline)
        if S is None:
            continue
        n, e = haar_from(MT, S, NN)
        try:
            ok = n > best_n and lib.is_valid(n, e, d, D)
        except Exception:
            ok = False
        if ok:
            best_n, best_edges = n, e

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
