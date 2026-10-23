"""Haar-graph annealing over metacyclic groups of order just above 2000 (d=10, D=5).

CONSTRUCTION.  Haar graph of a group G with connection set S (|S| = d):
A-vertex g ~ B-vertex s*g for s in S.  It is bipartite and d-regular on 2|G| vertices.
Right multiplication is an automorphism, so the diameter is <= 5 iff the balls of
radius 5 around the A-identity and the B-identity both cover the graph.

SEARCH.  For each candidate non-abelian metacyclic group Z_m x|_r Z_k with order N
(N just above the parent's 1791, aiming for N >= 2001 so that 2N beats 4000), run
simulated annealing on S, replacing one element at a time.  Cost = number of
(source, vertex) pairs not reached within radius 5.  Any zero-cost S is rebuilt into
an explicit edge list and checked with lib.is_valid before it is accepted.

SAFETY.  The parent's valid Haar graph (Z_199 x| Z_9, 3582 vertices) is verified first
and used as the fallback, so the output is never worse than that.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
D_TARGET = 5
DEG = 10
STEPS = 4000
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]

_OPT_CACHE = {}


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def group_table(m, k, r):
    """Z_m x|_r Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l).  Returns (MT, inv)."""
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


def metacyclic_opts(N):
    """Non-abelian metacyclic parameters (m, k, r) with m*k = N, cached."""
    if N in _OPT_CACHE:
        return _OPT_CACHE[N]
    out = []
    for m in range(3, N // 2 + 1):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append((m, k, r))
    _OPT_CACHE[N] = out
    return out


def pick_N(lo, rng):
    """Pick a group order in [lo, lo+60) that has non-abelian metacyclic options, biased to small N."""
    cands = []
    for N in range(lo, lo + 60):
        opts = metacyclic_opts(N)
        if opts:
            cands.append((N, opts))
    if not cands:
        return None
    i, j = int(rng.integers(len(cands))), int(rng.integers(len(cands)))
    return cands[min(i, j)]


def cost_fn(MT, inv, N, S):
    """Return (uncovered count, adjacency) for Haar graph of table group MT with set S."""
    adj = np.empty((2 * N, DEG), dtype=np.intp)
    adj[:N] = N + MT[S].T
    adj[N:] = MT[inv[S]].T
    reach = np.zeros((2, 2 * N), dtype=bool)
    reach[0, 0] = True
    reach[1, N] = True
    for _ in range(D_TARGET):
        reach = reach | reach[:, adj].any(axis=2)
    return 4 * N - int(np.count_nonzero(reach)), adj


def anneal(N, MT, inv, rng, deadline, steps):
    """Single-element annealing on S; returns (S, adj) at cost 0, or None."""
    S = rng.choice(N, DEG, replace=False).astype(np.int64)
    cur, adj = cost_fn(MT, inv, N, S)
    if cur == 0:
        return S, adj
    for step in range(steps):
        if time.monotonic() > deadline:
            return None
        i = int(rng.integers(DEG))
        g = int(rng.integers(N))
        if np.any(S == g):
            continue
        old = int(S[i])
        S[i] = g
        c, adj_new = cost_fn(MT, inv, N, S)
        temp = 0.2 + 1.5 * (1.0 - step / steps)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
            adj = adj_new
            if cur == 0:
                return S.copy(), adj
        else:
            S[i] = old
    return None


def haar_edges(N, MT, S):
    """Edge list of the Haar graph: A-vertex g is g, B-vertex y is N + y."""
    S = np.asarray(S, dtype=np.int64)
    A = np.repeat(np.arange(N, dtype=np.int64), len(S))
    B = (N + MT[S].T.astype(np.int64)).ravel()
    return list(zip(A.tolist(), B.tolist()))


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
        N = m * k
        e = haar_edges(N, MT, FALLBACK_S)
        if lib.is_valid(2 * N, e, d, D):
            best_n, best_edges = 2 * N, e
    except Exception:
        pass

    while time.monotonic() < deadline:
        lo = best_n // 2 + 1
        pick = pick_N(lo, rng)
        if pick is None:
            break
        N, opts = pick
        m, k, r = opts[int(rng.integers(len(opts)))]
        try:
            MT, inv = group_table(m, k, r)
            res = anneal(N, MT, inv, rng, deadline, STEPS)
        except Exception:
            res = None
        if res is None:
            continue
        S, _ = res
        try:
            e = haar_edges(N, MT, S)
            n = 2 * N
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_edges = n, e
        except Exception:
            pass

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
