import math
import random
import time
from math import gcd

import numpy as np
import lib


def _cyclic_fallback(d, D, seed, deadline):
    """Parent's cyclic Haar-graph search, used for diameters other than 5."""
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))          # complete bipartite K_{d,d}: always valid
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


def _group(N, rng):
    """Random semidirect product Z_m x| Z_k of order N = m*k (k small). Returns (m, k, r)."""
    ks = [k for k in range(1, min(N, 60) + 1) if N % k == 0]
    k = rng.choice(ks)
    m = N // k
    if m == 1:
        return 1, k, 0
    cands = [r for r in range(1, m) if gcd(r, m) == 1 and pow(r, k, m) == 1]
    nonab = [r for r in cands if r != 1]
    if nonab and rng.random() < 0.8:
        r = rng.choice(nonab)                   # prefer non-abelian groups
    else:
        r = rng.choice(cands)
    return m, k, r


def _mul_table(m, k, r, N):
    """Multiplication table of Z_m x| Z_k, element (a, b) coded as a*k+b, (a,b)(c,d) = (a + r^b c, b + d)."""
    x = np.arange(N, dtype=np.int64)
    a, b = x // k, x % k
    pw = np.array([pow(r, j, m) if m > 1 else 0 for j in range(k)], dtype=np.int64)
    table = np.empty((N, N), dtype=np.int32)
    for i0 in range(0, N, 256):
        i1 = min(N, i0 + 256)
        A = a[i0:i1, None]
        B = b[i0:i1, None]
        table[i0:i1] = ((A + pw[B] * a[None, :]) % m) * k + (B + b[None, :]) % k
    return table


def _cost(S, mul, inv, N):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2; zero means diameter <= 5 for the Haar graph."""
    S = np.asarray(S, dtype=np.int64)
    iS = inv[S]
    total = 0
    for L, R in ((iS, S), (S, iS)):
        X = np.unique(mul[L[:, None], R[None, :]]).astype(np.int64)
        Y = mul[X[:, None], X[None, :]]
        cov = np.zeros(N, dtype=bool)
        cov[Y.ravel()] = True
        total += N - int(np.count_nonzero(cov))
    return total


def _anneal(N, mul, inv, d, rng, deadline):
    """Simulated annealing over connection sets S of size d; returns a zero-cost S or None."""
    while time.monotonic() < deadline:
        S = rng.sample(range(N), d)
        cur = _cost(S, mul, inv, N)
        best_run = cur
        stall = 0
        T = 1.5
        while cur > 0 and stall < 4000:
            if time.monotonic() >= deadline:
                return None
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in S:
                stall += 1
                continue
            S2 = S[:]
            S2[i] = x
            c = _cost(S2, mul, inv, N)
            if c <= cur or rng.random() < math.exp(-(c - cur) / T):
                S, cur = S2, c
            if cur < best_run:
                best_run = cur
                stall = 0
            else:
                stall += 1
        if cur == 0:
            return S
    return None


def _haar(N, mul, S):
    """Haar graph over the group: A-vertex g is g, B-vertex g is N+g, edges (g,A) ~ (s*g, B)."""
    us = np.arange(N, dtype=np.int64)
    edges = []
    for s in S:
        vs = N + mul[s, us].astype(np.int64)
        edges.extend(zip(us.tolist(), vs.tolist()))
    return 2 * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    if D != 5:
        return _cyclic_fallback(d, D, seed, deadline)

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))          # always valid fallback
    lo, hi = 0, None                            # largest group order that succeeded / smallest that failed
    N = max(2 * d, 64)
    while time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        budget = min(remaining, max(3.0, 0.1 * time_limit))
        attempt_end = time.monotonic() + budget
        found = None
        while time.monotonic() < attempt_end and found is None:
            m, k, r = _group(N, rng)
            mul = _mul_table(m, k, r, N)
            inv = (mul == 0).argmax(axis=1)     # identity is code 0
            S = _anneal(N, mul, inv, d, rng, attempt_end)
            if S is None:
                continue
            n, edges = _haar(N, mul, S)
            if lib.is_valid(n, edges, d, D):
                found = (n, edges)

        if found:
            if found[0] > best[0]:
                best = found
            lo = N
            if hi is None:
                N = int(N * 1.2) + 1
            elif hi - lo > 1:
                N = (lo + hi) // 2
            else:
                N = hi                          # converged: keep retrying just above the last success
        else:
            hi = N
            N = (lo + hi) // 2 if hi - lo > 1 else hi
            if N <= lo:
                N = lo + 1
    return best
