"""Haar-graph word-cover annealing for the bipartite degree-diameter problem (d=10, D=5).

NEW HELPER: word_cost. For a Haar graph on a group G with connection set S, the diameter is at most 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G. word_cost counts the group elements missed by these two products. It is
evaluated with vectorised table lookups on the group multiplication table, so one evaluation costs
about d^4 lookups, far cheaper than a BFS on the 2N-vertex graph.

SEARCH. Simulated annealing over S (d distinct elements), with a single-slot replacement move and a
Metropolis rule. Each restart draws a random metacyclic group Z_m x| Z_k of order N just above the current
best. A zero-cost S gives a Haar graph on 2N vertices, which is checked with lib.is_valid before it is
accepted. The valid Haar graph of order 2*1791 is the fallback.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10

# Valid Haar fallback (group Z_199 x| Z_9, 1791 elements, 3582 vertices).
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------ groups

def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j and (a,j)(b,l) = (a + r^j b, j + l). Returns (MT, inv)."""
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
    """All (m, k, r) with m*k = N, k >= 2, gcd(r, m) = 1, r^k = 1 mod m, and r != 1 (non-abelian)."""
    opts = []
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    if not opts:
        opts = [(1, N, 1)]  # cyclic fallback
    return opts


# ------------------------------------------------------------------ word cover (new helper)

def cover_count(MT, N, X):
    """Number of distinct products x*y over x, y in X."""
    mark = np.zeros(N, dtype=bool)
    mark[MT[X[:, None], X[None, :]].ravel()] = True
    return int(mark.sum())


def word_cost(MT, inv, N, S):
    """Uncovered elements of (S^-1 S)^2 plus those of (S S^-1)^2. Zero iff the Haar graph has diameter <= 5."""
    Sa = np.asarray(S, dtype=np.int64)
    iS = inv[Sa]
    A = np.unique(MT[iS[:, None], Sa[None, :]]).astype(np.int64)  # s^-1 t
    B = np.unique(MT[Sa[:, None], iS[None, :]]).astype(np.int64)  # s t^-1
    return 2 * N - cover_count(MT, N, A) - cover_count(MT, N, B)


def anneal(MT, inv, N, d, rng, steps, deadline):
    """Simulated annealing on S; returns (S, cost). Stops early at cost 0 or the deadline."""
    S = [int(x) for x in rng.choice(N, d, replace=False)]
    cur = word_cost(MT, inv, N, S)
    for step in range(steps):
        if cur == 0:
            break
        if (step & 255) == 0 and time.monotonic() > deadline:
            break
        i = int(rng.integers(d))
        x = int(rng.integers(N))
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c = word_cost(MT, inv, N, S)
        temp = 1.5 * (1.0 - step / steps) + 0.1
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            S[i] = old
    return S, cur


def haar_from(MT, S, N):
    """Haar graph of the table group: (g, A) ~ (s*g, B), with A-vertex g as g and B-vertex g as N + g."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted(set(S)):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


# ------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.80 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_N, best_n, best_edges = 0, 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        n, e = haar_from(MT, FALLBACK_S, m * k)
        if lib.is_valid(n, e, d, D):
            best_N, best_n, best_edges = m * k, n, e
    except Exception:
        pass

    cache = {}
    cands = []
    cands_for = -1

    while time.monotonic() < deadline:
        if cands_for != best_N:
            cands = [N for N in range(best_N + 1, best_N + 200) if metacyclic_options(N)]
            cands_for = best_N
            if not cands:
                break
        # Bias towards the smallest candidate orders, which are the most likely to succeed.
        idx = min(len(cands) - 1, int(rng.exponential(3.0)))
        N = cands[idx]

        opts = metacyclic_options(N)
        m, k, r = opts[int(rng.integers(len(opts)))]
        key = (m, k, r)
        if key not in cache:
            if len(cache) >= 6:
                cache.clear()
            cache[key] = group_table(m, k, r)
        MT, inv = cache[key]

        slice_end = min(deadline, time.monotonic() + 8.0)
        while time.monotonic() < slice_end and cands_for == best_N:
            S, c = anneal(MT, inv, N, d, rng, 6000, slice_end)
            if c != 0:
                continue
            n, e = haar_from(MT, S, N)
            try:
                ok = n > best_n and lib.is_valid(n, e, d, D)
            except Exception:
                ok = False
            if ok:
                best_N, best_n, best_edges = N, n, e
                break

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
