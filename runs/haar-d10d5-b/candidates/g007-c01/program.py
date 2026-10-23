"""Haar-graph coverage search for the d=10, D=5 target.

NEW IDEA: batched best-of-K annealing with a count-based coverage cost.

A Haar graph over a group G with connection set S (|S| = d) has diameter <= 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G. The cost is the number of uncovered elements on both sides.
For a move that replaces one slot of S, K candidate sets are evaluated at once. The products
x*y over the pairs of difference-set elements are gathered as one (K, d^4) table lookup, and their
coverage is counted with a single np.bincount over per-candidate offset rows. This amortizes Python
overhead across candidates, which the parent's per-candidate BFS on the full graph does not do.

Groups are non-abelian metacyclic Z_m x| Z_k with order N just above 2000, so 2N > 4000 vertices.
Any zero-cost set is checked with lib.is_valid. A valid 3582-vertex Haar graph is the fallback.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)

# Valid Haar fallback (group Z_199 x| Z_9, 1791 elements, 3582 vertices).
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]

STALL = 1200   # steps without improvement before a restart
K = 32         # candidates evaluated per annealing step
SLICE = 7.0    # seconds per (group, annealing run)


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------ groups

def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l). Returns (MT, inv)."""
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
    """All (m, k, r) with m*k = N, k >= 2, and a non-trivial action r (so the group is non-abelian)."""
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


# ------------------------------------------------------------------------------ cost

def batch_costs(MT, inv, N, Sb, d):
    """Coverage cost for K candidate sets Sb (K x d, distinct entries per row).

    cost = (N - |(S^-1 S)^2|) + (N - |(S S^-1)^2|), computed for all K rows in one pass.
    """
    K_ = Sb.shape[0]
    Si = inv[Sb]
    base = (np.arange(K_, dtype=np.int64) * N)[:, None]
    # S^-1 S and its square-products
    X = MT[Si[:, :, None], Sb[:, None, :]].reshape(K_, d * d)
    Y = MT[X[:, :, None], X[:, None, :]].reshape(K_, -1).astype(np.int64) + base
    cY = np.bincount(Y.ravel(), minlength=K_ * N).reshape(K_, N)
    # S S^-1 and its square-products
    Z = MT[Sb[:, :, None], Si[:, None, :]].reshape(K_, d * d)
    W = MT[Z[:, :, None], Z[:, None, :]].reshape(K_, -1).astype(np.int64) + base
    cW = np.bincount(W.ravel(), minlength=K_ * N).reshape(K_, N)
    return 2 * N - np.count_nonzero(cY, axis=1) - np.count_nonzero(cW, axis=1)


def anneal(MT, inv, N, d, rng, deadline):
    """Batched best-of-K annealing on S. Returns a zero-cost S, or None on stall or deadline."""
    S = rng.choice(N, size=d, replace=False).astype(np.int64)
    cur = int(batch_costs(MT, inv, N, S[None, :], d)[0])
    best = cur
    stall = 0
    while time.monotonic() < deadline:
        if cur == 0:
            return S
        if stall > STALL:
            return None
        i = int(rng.integers(d))
        cand = rng.integers(N, size=K).astype(np.int64)
        ok = ~np.isin(cand, S)
        if not ok.any():
            stall += 1
            continue
        cand = cand[ok]
        Sb = np.tile(S, (len(cand), 1))
        Sb[:, i] = cand
        costs = batch_costs(MT, inv, N, Sb, d)
        kb = int(np.argmin(costs))
        c = int(costs[kb])
        T = max(0.2, 1.5 * (1.0 - stall / STALL))
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            S = Sb[kb].copy()
            cur = c
        if cur < best:
            best = cur
            stall = 0
        else:
            stall += 1
    return None


def haar_edges(MT, S, N):
    """Haar graph: A-vertex g is g, B-vertex g is N + g, and (g, A) ~ (s*g, B) for s in S."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted({int(x) for x in S}):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


# ------------------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(3.0, min(0.75 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        n, e = haar_edges(MT, FALLBACK_S, m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    # Candidate group orders N > 2000 (so 2N > 4000) that admit a non-abelian metacyclic group.
    pool = []
    for N in range(2001, 2061):
        opts = metacyclic_options(N)
        if opts:
            pool.append((N, opts))

    while pool and time.monotonic() < deadline - 2.0:
        N, opts = pool[int(rng.integers(len(pool)))]
        m, k, r = opts[int(rng.integers(len(opts)))]
        try:
            MT, inv = group_table(m, k, r)
            seg = min(deadline, time.monotonic() + SLICE)
            S = anneal(MT, inv, N, d, rng, seg)
            if S is not None:
                n, e = haar_edges(MT, S, N)
                if n > best_n and lib.is_valid(n, e, d, D):
                    best_n, best_edges = n, e
                    pool = [(NN, o) for NN, o in pool if 2 * NN > best_n]
        except Exception:
            continue

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
