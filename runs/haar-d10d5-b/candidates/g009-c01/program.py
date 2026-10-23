"""Haar-graph annealing for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  Take a metacyclic group G = Z_m x|_r Z_k of order N and a connection set S of d = 10 distinct
elements.  The Haar graph has vertices A_g = g and B_g = N + g, with edges A_g ~ B_{s*g} for s in S.  It is bipartite,
d-regular, and has 2N vertices.  Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.

SEARCH.  For each group order N just above the current best, pick a random non-abelian metacyclic group of order N
and run simulated annealing on S.  Each step replaces one element of S and recomputes the full cost, which is the
number of uncovered group elements in the two word sets.  Cost is evaluated with small numpy lookups, so no
incremental bookkeeping is needed.  A zero-cost S is checked with lib.is_valid before it replaces the incumbent.
The valid Haar fallback (Z_199 x| Z_9, 3582 vertices) is kept, so the output is never worse than the parent's.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
STEPS = 12000
WINDOW = 150

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


def metacyclic_params(N):
    """All (m, k, r) with m*k = N, k >= 2, r != 1 giving a valid non-abelian semidirect product."""
    out = []
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def covered(Q, N):
    mark = np.zeros(N, dtype=bool)
    mark[Q] = True
    return int(np.count_nonzero(mark))


def cost(MT, inv, S, N):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2; zero iff the Haar graph has diameter <= 5."""
    Si = inv[S]
    P = MT[Si[:, None], S[None, :]].astype(np.int64).ravel()   # s^-1 t
    R = MT[S[:, None], Si[None, :]].astype(np.int64).ravel()   # s t^-1
    c1 = covered(MT[P[:, None], P[None, :]].ravel(), N)
    c2 = covered(MT[R[:, None], R[None, :]].ravel(), N)
    return 2 * N - c1 - c2


def anneal(MT, inv, N, d, rng, steps, deadline):
    """Simulated annealing over S; returns a zero-cost S (numpy array) or None."""
    S = rng.choice(N, d, replace=False).astype(np.int64)
    cur = cost(MT, inv, S, N)
    for step in range(steps):
        if cur == 0:
            return S.copy()
        if time.monotonic() > deadline:
            return None
        i = int(rng.integers(d))
        x = int(rng.integers(N))
        if np.any(S == x):
            continue
        old = int(S[i])
        S[i] = x
        c = cost(MT, inv, S, N)
        temp = 1.5 * (1.0 - step / steps) + 0.1
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            S[i] = old
    return S.copy() if cur == 0 else None


def haar_from(MT, S, N):
    """Haar graph of the table group: (g, A) ~ (s*g, B), vertices A = g, B = N + g."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted(set(int(x) for x in S)):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.80 * time_limit, time_limit - 8.0))
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

    cache = {}
    while time.monotonic() < deadline:
        lo = best_n // 2 + 1
        hi = lo + WINDOW
        N = int(rng.integers(lo, hi + 1))
        if N not in cache:
            cache[N] = metacyclic_params(N)
        params = cache[N]
        if not params:
            continue
        m, k, r = params[int(rng.integers(len(params)))]
        try:
            MT, inv = group_table(m, k, r)
            S = anneal(MT, inv, N, d, rng, STEPS, deadline)
        except Exception:
            continue
        if S is None:
            continue
        n, e = haar_from(MT, S, N)
        try:
            ok = n > best_n and lib.is_valid(n, e, d, D)
        except Exception:
            ok = False
        if ok:
            best_n, best_edges = n, e

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
