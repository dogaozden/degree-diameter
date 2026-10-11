import math
import random
import time
from math import gcd

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe fallbacks.
# ----------------------------------------------------------------------------

def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over small groups (one orbit per side).
#
# Group G of order N, connection set S of size d.
# Vertices: a_g = g and b_h = N + h.  Edge a_g -- b_{g*s} for s in S.
#
# Left translation by x maps a_g -> a_{xg}, b_h -> b_{xh} and preserves edges,
# so the automorphism group is transitive on each side. Hence the diameter is
# at most D iff every vertex is within distance D of a_e and of b_e.
# That needs only two BFS runs, so the search is cheap.
# ----------------------------------------------------------------------------

def _group_table(m, k, r):
    """Full multiplication table T[x, y] = x*y for Z_m x|_r Z_k, element (a, b) coded as a*k + b."""
    N = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    a, b = x // k, x % k
    A, B = a[:, None], b[:, None]
    C, E = a[None, :], b[None, :]
    return ((A + pw[B] * C) % m) * k + (B + E) % k


def _group_candidates(N, rng):
    """(m, k, r) triples giving groups of order N: cyclic, plus a few semidirect products."""
    out = []
    for k in range(1, N // 2 + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m) if gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        out.extend((m, k, r) for r in rs[:3])
    rng.shuffle(out)
    return out


def _cost(T, inv, S, N, D):
    """Number of (source, vertex) pairs not reached within D, over sources a_e and b_e. Zero means valid."""
    Si = inv[S]
    total = 0
    for side in (0, 1):
        seen_a = np.zeros(N, dtype=bool)
        seen_b = np.zeros(N, dtype=bool)
        empty = np.empty(0, dtype=np.int64)
        if side == 0:
            seen_a[0] = True
            fa, fb = np.array([0], dtype=np.int64), empty
        else:
            seen_b[0] = True
            fa, fb = empty, np.array([0], dtype=np.int64)
        for _ in range(D):
            if fa.size == 0 and fb.size == 0:
                break
            na = T[fb][:, Si].ravel()
            nb = T[fa][:, S].ravel()
            na = np.unique(na)
            na = na[~seen_a[na]]
            nb = np.unique(nb)
            nb = nb[~seen_b[nb]]
            seen_a[na] = True
            seen_b[nb] = True
            fa, fb = na, nb
        total += 2 * N - int(seen_a.sum()) - int(seen_b.sum())
    return total


def _search(T, inv, N, d, D, rng, deadline, iters):
    """Simulated annealing over the connection set S (|S| = d). Returns (S or None, cost)."""
    S = np.array(rng.sample(range(N), d), dtype=np.int64)
    c = _cost(T, inv, S, N, D)
    temp = 3.0
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(N)
        if (S == x).any():
            continue
        S2 = S.copy()
        S2[i] = x
        c2 = _cost(T, inv, S2, N, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            S, c = S2, c2
        temp = max(0.3, temp * 0.9995)
    return (S if c == 0 else None), c


def _bicayley_edges(N, T, S):
    """Edges of the bi-Cayley graph: a_g -- b_{T[g, s]} for s in S."""
    edges = []
    for g in range(N):
        for s in S:
            edges.append((g, N + int(T[g, s])))
    return 2 * N, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Bi-Cayley search: N = order of the group, graph order 2N.
    # Start just above the record-scale range and climb N while N is below the Moore limit.
    moore = lib._moore_bound(d, D)
    Nmax = moore // 2
    lo = max(best_n // 2 + 1, int(0.44 * Nmax))
    N = lo
    SLICE = 3.0
    while N <= Nmax and time.monotonic() < deadline:
        slice_end = min(deadline, time.monotonic() + SLICE)
        for m, k, r in _group_candidates(N, rng):
            if time.monotonic() >= slice_end:
                break
            T = _group_table(m, k, r)
            inv = np.argmax(T == 0, axis=1)
            S, _ = _search(T, inv, N, d, D, rng, slice_end, 2500)
            if S is not None:
                n, e = _bicayley_edges(N, T, S)
                consider(n, e)
                break
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
