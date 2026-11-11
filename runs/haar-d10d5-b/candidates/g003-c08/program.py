"""Haar-graph search with a pair-covering cost for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  For a group G of order N and a set S of d distinct elements, the Haar graph has vertices
A_g and B_g (g in G) and edges A_g ~ B_{s*g} for s in S.  It is bipartite and d-regular on 2N vertices.
Its diameter is at most 5 when (S^-1 S)^2 = G and (S S^-1)^2 = G.

NEW HELPER.  pair_cost(S) counts the group elements not covered by the two squared difference sets.
It is computed with one 2-D table gather and a boolean mark per set, so each evaluation costs about
100 microseconds.  Annealing swaps one element of S at a time and accepts moves by the Metropolis rule.
Each zero-cost set is checked with lib.is_valid before it is accepted.

SEARCH.  Random metacyclic groups Z_m x|_r Z_k with N just above the threshold 1792 (which gives 2N > 3582).
The search runs restarts until the deadline.  The valid parent Haar graph of order 3582 is the fallback, so
the output is never worse than before.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
TARGET_D = 10
NMIN = 1792
NMAX = 1900

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


def pick_group(N, rng):
    """Random metacyclic (m, k, r) with m*k = N, preferring non-abelian choices."""
    options = []
    for m in range(2, N):
        if N % m != 0:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                options.append((m, k, r))
    if not options:
        return (1, N, 1)  # cyclic fallback
    return options[int(rng.integers(len(options)))]


def pair_cost(S, MT, inv, N):
    """Uncovered elements of (S^-1 S)^2 plus uncovered elements of (S S^-1)^2.  Zero means diameter <= 5."""
    Si = inv[S]
    total = 0
    for P in (np.unique(MT[Si[:, None], S[None, :]]),
              np.unique(MT[S[:, None], Si[None, :]])):
        Q = MT[P[:, None], P[None, :]].ravel()
        mark = np.zeros(N, dtype=bool)
        mark[Q] = True
        total += N - int(np.count_nonzero(mark))
    return total


def anneal(MT, inv, N, d, rng, deadline):
    """Simulated annealing over d-subsets of G with restarts.  Returns a zero-cost S or None."""
    L = 20000
    while time.monotonic() < deadline:
        S = rng.choice(N, d, replace=False).astype(np.int64)
        cur = pair_cost(S, MT, inv, N)
        for step in range(L):
            if (step & 63) == 0 and time.monotonic() > deadline:
                return None
            if cur == 0:
                return S
            pos = int(rng.integers(d))
            new = int(rng.integers(N))
            if np.any(S == new):
                continue
            S2 = S.copy()
            S2[pos] = new
            c = pair_cost(S2, MT, inv, N)
            if c == 0:
                return S2
            temp = 2.0 * (1.0 - step / L) + 0.05
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                S, cur = S2, c
    return None


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
        lo = max(NMIN, best_n // 2 + 1)
        hi = max(lo, NMAX)
        N = int(rng.integers(lo, hi + 1))
        try:
            m, k, r = pick_group(N, rng)
            MT, inv = group_table(m, k, r)
            S = anneal(MT, inv, N, d, rng, deadline)
        except Exception:
            S = None
        if S is None:
            if time.monotonic() >= deadline:
                break
            continue
        try:
            n, e = haar_from(MT, S, N)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_edges = n, e
        except Exception:
            pass

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
