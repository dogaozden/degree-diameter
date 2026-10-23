import math
import random
import time

import numpy as np
import lib


def _cyclic_search(d, D, rng, deadline):
    """Parent's cyclic Haar search: returns the largest valid cyclic Haar graph found before the deadline."""
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


def _groups_of_order(N):
    """All metacyclic groups Z_m x| Z_k (m*k = N) given as (m, k, r), with r^k = 1 mod m and gcd(r, m) = 1."""
    out = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _group_tables(m, k, r):
    """Multiplication and inverse tables for the element (a, b) coded as a*k + b, with (a,b)(c,d) = (a + r^b c, b + d)."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a, b = x // k, x % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    A, B = a[:, None], b[:, None]
    C, Dd = a[None, :], b[None, :]
    T = ((A + pw[B] * C) % m) * k + (B + Dd) % k
    inv = np.argmax(T == 0, axis=1)  # identity is element 0
    return N, T.tolist(), inv.tolist()


def _cost(N, M, I, S):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2; zero exactly when the Haar graph has diameter <= 5."""
    T = {M[I[s]][t] for s in S for t in S}
    U = {M[s][I[t]] for s in S for t in S}
    T2 = {M[x][y] for x in T for y in T}
    U2 = {M[x][y] for x in U for y in U}
    return 2 * N - len(T2) - len(U2)


def _anneal(N, M, I, d, rng, steps, deadline, temp=0.8):
    """Simulated annealing over connection sets S of size d. Returns S with cost 0, or None."""
    S = rng.sample(range(N), d)
    cur = _cost(N, M, I, S)
    for _ in range(steps):
        if cur == 0:
            break
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        g = rng.randrange(N)
        if g in S:
            continue
        old = S[i]
        S[i] = g
        c = _cost(N, M, I, S)
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            S[i] = old
    return S if cur == 0 else None


def _haar_from_group(N, M, S):
    """Haar graph over group G: A-vertex g is g, B-vertex h is N + h; edges g ~ N + s*g for s in S."""
    edges = [(g, N + M[s][g]) for g in range(N) for s in S]
    return 2 * N, edges


def _group_search(d, D, rng, best, deadline):
    """Search non-abelian and abelian metacyclic groups of order just above the record for a valid Haar graph."""
    best_N = best[0] // 2
    cand = []
    for N in range(343, 401):
        gs = _groups_of_order(N)
        rng.shuffle(gs)
        cand.extend((N, g) for g in gs[:4])
    cache = {}
    rnd = 0
    while time.monotonic() < deadline and rnd <= 40:
        steps = 600 << min(rnd, 6)
        for N, grp in cand:
            if time.monotonic() >= deadline:
                break
            if N <= best_N:
                continue
            if grp not in cache:
                cache[grp] = _group_tables(*grp)
            _, M, I = cache[grp]
            S = _anneal(N, M, I, d, rng, steps, deadline)
            if S is None:
                continue
            n, edges = _haar_from_group(N, M, S)
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_N = N
        rnd += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    rng = random.Random(seed)
    if D != 5 or d < 3:
        return _cyclic_search(d, D, rng, deadline)
    # Diameter 5: quick cyclic fallback, then group-based Haar search for orders above the record.
    best = _cyclic_search(d, D, rng, start + 0.12 * time_limit)
    best = _group_search(d, D, rng, best, deadline)
    n, edges = best
    if lib.is_valid(n, edges, d, D):
        return best
    return lib.haar_graph(d, range(d))
