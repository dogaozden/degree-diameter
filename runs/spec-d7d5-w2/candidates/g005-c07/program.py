"""Bipartite double covers of Cayley graphs, found by simulated annealing.

For a finite group G of order N and a set S of d distinct elements, the bipartite
double cover has vertices (g, 0) and (g, 1) for g in G, with edges (g, 0)-(g*s, 1)
for s in S. It is d-regular and bipartite, and it has 2N vertices. Left
multiplication is an automorphism, so the diameter is determined by BFS from
(e, 0) and (e, 1) alone. Annealing over S minimises the number of unreached pairs.

The order N grows from a low start with an adaptive step. Every candidate is
checked with lib.is_valid. The K_{d,d} fallback, and the projective-plane
incidence graph when D = 3, are always available.
"""
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact or easy fallbacks.
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Groups Z_m x|_r Z_k, element a*k + b, with (a,b)(c,e) = (a + r^b c, b + e).
# ----------------------------------------------------------------------------

def _group_candidates(N, rng, cap=60):
    """Return shuffled (m, k, r) with m*k = N and r^k = 1 mod m, gcd(r, m) = 1."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        out.append((m, k, 1))
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    rng.shuffle(out)
    return out[:cap]


def _table(m, k, r):
    """Multiplication table M (N x N) and inverse vector Minv for the semidirect group."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    M = A * k + (b[:, None] + b[None, :]) % k
    Minv = np.argmax(M == 0, axis=1).astype(np.int64)
    return M, Minv


# ----------------------------------------------------------------------------
# Double-cover cost: number of (source, vertex) pairs at distance > D.
# ----------------------------------------------------------------------------

def _cost(M, Minv, N, d, D, S):
    nbr = np.empty((2 * N, d), dtype=np.int64)
    nbr[:N] = N + M[:, S]          # (g, 0) ~ (g*s, 1)
    nbr[N:] = M[:, Minv[S]]        # (h, 1) ~ (h*s^{-1}, 0)
    total = 0
    N2 = 2 * N
    for src in (0, N):
        reach = np.zeros(N2, dtype=bool)
        reach[src] = True
        for _ in range(D):
            idx = np.flatnonzero(reach)
            nxt = reach.copy()
            nxt[nbr[idx].ravel()] = True
            if int(nxt.sum()) == int(reach.sum()):
                break
            reach = nxt
        total += N2 - int(reach.sum())
    return total


def _sa(M, Minv, N, d, D, rng, iters, deadline):
    """Anneal a d-subset S of G to make the double cover of diameter <= D. Returns S or None."""
    S = np.array(rng.sample(range(N), d), dtype=np.int64)
    cost = _cost(M, Minv, N, d, D, S)
    for t in range(iters):
        if cost == 0:
            return S
        if (t & 63) == 0 and time.monotonic() > deadline:
            break
        j = rng.randrange(d)
        new = rng.randrange(N)
        if np.any(S == new):
            continue
        old = int(S[j])
        S[j] = new
        c2 = _cost(M, Minv, N, d, D, S)
        T = 1.5 * (1.0 - t / iters) + 0.05
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            S[j] = old
    return S if cost == 0 else None


def _attempt(N, d, D, rng, deadline, iters):
    """Try groups of order N until one yields a valid S. Returns (M, S) or None."""
    for (m, k, r) in _group_candidates(N, rng):
        if time.monotonic() > deadline:
            break
        M, Minv = _table(m, k, r)
        S = _sa(M, Minv, N, d, D, rng, iters, deadline)
        if S is not None:
            return M, S
    return None


def _edges(M, S, N, d):
    rows = np.repeat(np.arange(N, dtype=np.int64), d)
    cols = N + M[:, S].ravel()
    return list(zip(rows.tolist(), cols.tolist()))


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.88 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))[0], lib.haar_graph(d, range(d))[1]
    if D == 2:
        return best_n, best_e

    if D >= 3:
        pg = _pg_best(d)
        if pg is not None and lib.is_valid(pg[0], pg[1], d, D) and pg[0] > best_n:
            best_n, best_e = pg
            if D == 3 and lib.is_prime_power(d - 1):
                return best_n, best_e

    # Adaptive growth of N, the group order; the graph has 2N vertices.
    mb = lib.moore_bound(d, D)
    N = max(d + 1, int(0.30 * mb / 2))
    step = 8
    fails = 0
    while time.monotonic() < deadline:
        now = time.monotonic()
        remaining = deadline - now
        attempt_deadline = now + min(remaining, max(2.0, 0.2 * remaining))
        tgt = N + step
        res = _attempt(tgt, d, D, rng, attempt_deadline, iters=2500)
        if res is not None:
            M, S = res
            edges = _edges(M, S, tgt, d)
            n = 2 * tgt
            if n > best_n and lib.is_valid(n, edges, d, D):
                best_n, best_e = n, edges
                N = tgt
                step = min(step * 2, 32)
                fails = 0
                continue
        if step == 1:
            fails += 1
            if fails >= 2:
                break
        else:
            step = max(1, step // 2)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
