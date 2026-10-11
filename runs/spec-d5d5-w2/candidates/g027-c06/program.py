import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x|_r Z_k, searched with a
# vectorised bitset-style BFS evaluator and simulated annealing.
#
# A bi-Cayley graph on groups of order N has vertices A_x, B_y (x, y in G) with
# A_x ~ B_{x g} for g in S, |S| = d. Left translation is an automorphism, so the
# diameter is at most D iff the eccentricities of A_0 and B_0 are at most D.
# This is a different search space from the parent's pure-Python hill climb:
# the evaluator is numpy-vectorised, the annealer accepts uphill moves, and the
# group sweep wraps around within a band instead of marching forever.
# ----------------------------------------------------------------------------

MAX_GROUPS = 6        # groups tried per order N before moving on
ANNEAL_ITERS = 2500   # annealing steps per group
BAND = 40             # orders swept above the current target before wrapping


def _fallback(d, D):
    """Always-valid baseline graphs for small or degenerate cases."""
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D  # even cycle of length 2D: bipartite, diameter D, Moore-optimal
        return L, [(i, (i + 1) % L) for i in range(L)]
    return lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _perm_table(m, k, r):
    """P[g, x] = x*g in Z_m x|_r Z_k (element (a, b) coded as a*k + b), plus inverses.

    Multiplication: (a, b)(c, d) = (a + r^b c, b + d), identity coded as 0.
    """
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    P = np.empty((N, N), dtype=np.int64)
    for g in range(N):
        c, dd = divmod(g, k)
        P[g] = ((a + pw[b] * c) % m) * k + (b + dd) % k
    invs = np.array([int(np.flatnonzero(P[g] == 0)[0]) for g in range(N)], dtype=np.int64)
    return P, invs


def _unreached(N, P, invs, S, D):
    """Number of (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    Sarr = list(S)
    Sinv = [int(invs[g]) for g in S]
    total = 0
    for side in (0, 1):
        visA = np.zeros(N, dtype=bool)
        visB = np.zeros(N, dtype=bool)
        if side == 0:
            visA[0] = True
            fA = np.array([0], dtype=np.int64)
            fB = np.empty(0, dtype=np.int64)
        else:
            visB[0] = True
            fB = np.array([0], dtype=np.int64)
            fA = np.empty(0, dtype=np.int64)
        for _ in range(D):
            if fA.size == 0 and fB.size == 0:
                break
            nB = np.zeros(N, dtype=bool)
            for g in Sarr:
                nB[P[g][fA]] = True
            nA = np.zeros(N, dtype=bool)
            for h in Sinv:
                nA[P[h][fB]] = True
            nB &= ~visB
            nA &= ~visA
            visB |= nB
            visA |= nA
            fA = np.flatnonzero(nA)
            fB = np.flatnonzero(nB)
        total += 2 * N - int(visA.sum()) - int(visB.sum())
    return total


def _anneal(N, P, invs, d, D, rng, deadline, iters):
    """Simulated annealing over connection sets S (identity fixed in S, WLOG)."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cost = _unreached(N, P, invs, S, D)
    T = 3.0
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, P, invs, S2, D)
        delta = v - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S, cost = S2, v
        T = max(0.5, T * 0.999)
    return S if cost == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    best = _fallback(d, D)
    if D <= 2 or d <= 2:
        return best  # fallbacks already meet the Moore bound here

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # D = 3 with d - 1 a prime power: projective plane incidence graph is Moore-optimal.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if best[0] >= moore:
        return best

    # Main search: bi-Cayley lifts on groups of order N, giving 2N vertices.
    half = moore // 2
    N = max(d, best[0] // 2 + 1)
    window_start = N
    while time.monotonic() < deadline and N <= half:
        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for (m, k, r) in groups[:MAX_GROUPS]:
            if time.monotonic() >= deadline:
                break
            P, invs = _perm_table(m, k, r)
            S = _anneal(N, P, invs, d, D, rng, deadline, ANNEAL_ITERS)
            if S is not None:
                found = (P, S)
                break
        if found is not None:
            P, S = found
            edges = [(x, N + int(P[g, x])) for x in range(N) for g in S]
            consider(2 * N, edges)
            window_start = N + 1
        N += 1
        if N - window_start > BAND:
            N = max(d, best[0] // 2 + 1)
            window_start = N

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d, D)
    return best
