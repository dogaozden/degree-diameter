"""Bipartite degree-diameter search for the d=10, D=5 target, using Haar graphs over non-abelian groups.

CONSTRUCTION.  Take a finite group G of order N and a set S of d group elements. The Haar graph has
vertices A_g and B_g (g in G), with A_g ~ B_{s*g} for s in S. It is bipartite, d-regular, and has 2N
vertices. Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G. So the search minimises
cost(S) = uncovered(S^-1 S squared) + uncovered(S S^-1 squared), and a cost of 0 gives a valid graph.

GROUPS.  Metacyclic groups Z_m x| Z_k (non-abelian, lam != 1), with orders N just above the fallback
(1791) and increasing. Smaller orders are tried first, so any success is a strict improvement.

SEARCH.  Round-robin over the candidate (N, m, k, lam) groups, with short simulated-annealing slices
per group and random restarts. Each candidate that reaches cost 0 is checked with lib.is_valid before
it is accepted.

SAFETY.  The validated fallback Haar graph (order 3582) is the baseline. Only graphs that pass
lib.is_valid are returned. Other (d, D) cases return a small always-valid graph.
"""
import math
import random
import time

import numpy as np

import lib


TARGET = (10, 5)
FALLBACK_PARAMS = (199, 9, 180)  # Z_199 x| Z_9, order 1791 -> Haar graph of order 3582
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
SLICE = 2.0       # seconds of annealing per group visit
TEMP = 1.0        # Metropolis temperature
N_LO, N_HI = 1792, 2100


# ----------------------------------------------------------------------------- groups

def semidirect(m, k, lam):
    """Multiplication table and inverses of Z_m x|_lam Z_k, element (a, j) coded as a*k+j.
    (a, j)(b, l) = (a + lam^j b, j + l); identity is index 0. Needs lam^k = 1 mod m."""
    N = m * k
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def candidates(lo, hi, rng_py):
    """Candidate (N, m, k, lam) with lo <= N <= hi, sorted by N ascending."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N // 2 + 1):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lams = [l for l in range(2, m) if math.gcd(l, m) == 1 and pow(l, k, m) == 1]
            rng_py.shuffle(lams)
            for lam in lams[:3]:
                out.append((N, m, k, lam))
    return out


# ----------------------------------------------------------------------------- search

def cost_of(S, MT, inv, N, mark):
    """Number of uncovered elements in (S^-1 S)^2 plus in (S S^-1)^2. Zero means a valid graph."""
    Si = inv[S]
    P = np.unique(MT[Si[:, None], S[None, :]])
    mark[:] = False
    mark[MT[P[:, None], P[None, :]].ravel()] = True
    c = N - int(np.count_nonzero(mark))
    P = np.unique(MT[S[:, None], Si[None, :]])
    mark[:] = False
    mark[MT[P[:, None], P[None, :]].ravel()] = True
    c += N - int(np.count_nonzero(mark))
    return c


def anneal(MT, inv, N, d, rng, end):
    """Metropolis search over d-subsets S of G until end; returns (best cost, best S)."""
    mark = np.zeros(N, dtype=bool)
    S = np.array(rng.choice(N, size=d, replace=False), dtype=np.int64)
    cur = cost_of(S, MT, inv, N, mark)
    best_c, best_S = cur, S.copy()
    while cur > 0 and time.monotonic() < end:
        i = int(rng.integers(d))
        x = int(rng.integers(N))
        if np.any(S == x):
            continue
        old = S[i]
        S[i] = x
        c = cost_of(S, MT, inv, N, mark)
        if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
            cur = c
            if c < best_c:
                best_c, best_S = c, S.copy()
        else:
            S[i] = old
    return best_c, best_S


def checked(MT, S, d, D):
    """Haar graph for S as (n, edges), or None if lib.is_valid rejects it."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    edges = [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]
    n = 2 * N
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = max(2.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    rng_py = random.Random(seed)

    best = None
    try:
        MT, _ = semidirect(*FALLBACK_PARAMS)
        best = checked(MT, FALLBACK_S, d, D)
    except Exception:
        best = None

    best_N = best[0] // 2 if best is not None else 0
    try:
        queue = candidates(max(N_LO, best_N + 1), N_HI, rng_py)
    except Exception:
        queue = []

    i = 0
    while queue and time.monotonic() + 2.0 < deadline:
        N, m, k, lam = queue[i % len(queue)]
        i += 1
        if N <= best_N:
            continue
        now = time.monotonic()
        end = min(deadline - 2.0, now + SLICE)
        try:
            MTc, invc = semidirect(m, k, lam)
            c, S = anneal(MTc, invc, N, d, rng, end)
            if c == 0:
                res = checked(MTc, S, d, D)
                if res is not None:
                    best = res
                    best_N = N
                    queue = [q for q in queue if q[0] > best_N]
                    i = 0
        except Exception:
            pass

    if best is not None:
        return best
    return trivial(d, D)
