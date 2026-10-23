import math
import random
import time
from math import gcd

import numpy as np
import lib


def _parent_cyclic(d, D, rng, deadline):
    """Random cyclic Haar search (the parent's method). Returns (n, edges)."""
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def _tables(m, k, r):
    """Multiplication and inverse tables of Z_m x|_r Z_k, element (a, b) coded as a*k+b."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a, b = x // k, x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    first = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    second = (b[:, None] + b[None, :]) % k
    mul = (first * k + second).astype(np.int32)
    nb = (-b) % k
    inv = ((-pw[nb] * a) % m) * k + nb
    return N, mul, inv.astype(np.int64)


def _cost(S, iS, mul, N):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2; zero iff the Haar graph has diameter <= 5."""
    L = mul[iS[:, None], S[None, :]].ravel()
    LL = mul[L[:, None], L[None, :]].ravel()
    seen = np.zeros(N, dtype=bool)
    seen[LL] = True
    c = N - int(np.count_nonzero(seen))
    R = mul[S[:, None], iS[None, :]].ravel()
    RR = mul[R[:, None], R[None, :]].ravel()
    seen[:] = False
    seen[RR] = True
    return c + N - int(np.count_nonzero(seen))


def _anneal(N, mul, inv, d, rng, deadline):
    """Simulated annealing over connection sets S (identity fixed in slot 0). Returns S or None."""
    limit = 30000
    while time.monotonic() < deadline:
        S = np.array([0] + rng.sample(range(1, N), d - 1), dtype=np.int64)
        iS = inv[S]
        cur = _cost(S, iS, mul, N)
        steps = 0
        while cur > 0 and steps < limit:
            if (steps & 255) == 0 and time.monotonic() >= deadline:
                return None
            steps += 1
            i = rng.randrange(1, d)
            x = rng.randrange(1, N)
            if x in S:
                continue
            S2 = S.copy()
            S2[i] = x
            iS2 = inv[S2]
            c = _cost(S2, iS2, mul, N)
            T = 1.5 * (0.05 / 1.5) ** (steps / limit)
            if c <= cur or rng.random() < math.exp(-(c - cur) / T):
                S, iS, cur = S2, iS2, c
        if cur == 0:
            return S
    return None


def _groups(lo, hi):
    """Candidate (m, k, r) for nonabelian Z_m x|_r Z_k with order m*k in [lo, hi]."""
    out = []
    for k in range(2, 13):
        for m in range(max(3, lo // k), hi // k + 1):
            N = m * k
            if N < lo or N > hi:
                continue
            for r in range(2, m):
                if gcd(r, m) == 1 and pow(r, k, m) == 1:
                    out.append((m, k, r))
    return out


def _haar_edges(N, mul, S):
    """Haar graph: A-vertex g joined to B-vertex N + s*g for each s in S."""
    edges = []
    for s in S.tolist():
        row = mul[s].tolist()
        for g in range(N):
            edges.append((g, N + row[g]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.8 * time_limit
    deadline = start + total
    rng = random.Random(seed)

    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D != 5 or d < 3:
        return _parent_cyclic(d, D, rng, deadline)

    # Phase 1: cyclic baseline for a short slice of the budget.
    best_n, best_e = _parent_cyclic(d, D, rng, start + 0.15 * total)

    # Phase 2: non-abelian Haar graphs, annealed connection sets.
    try:
        lo_N = best_n // 2 + 1
        cands = _groups(lo_N, 2600)
        rng.shuffle(cands)
        for (m, k, r) in cands:
            if time.monotonic() >= deadline:
                break
            N = m * k
            if 2 * N <= best_n:
                continue
            slice_end = min(deadline, time.monotonic() + 4.0)
            N, mul, inv = _tables(m, k, r)
            S = _anneal(N, mul, inv, d, rng, slice_end)
            if S is None:
                continue
            edges = _haar_edges(N, mul, S)
            if lib.is_valid(2 * N, edges, d, D) and 2 * N > best_n:
                best_n, best_e = 2 * N, edges
    except Exception:
        pass

    return best_n, best_e
