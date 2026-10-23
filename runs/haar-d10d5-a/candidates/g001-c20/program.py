import math
import random
import time

import numpy as np

import lib


def _groups_for(N):
    """Metacyclic groups Z_m x| Z_k (order N) given as (m, k, r): r^k = 1 mod m, gcd(r, m) = 1, r != 1."""
    out = []
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append((m, k, r))
    return out


def _metacyclic_table(m, k, r):
    """Full Cayley table of Z_m x| Z_k, element (a, b) coded a*k + b, (a,b)(c,d) = (a + r^b c, b + d)."""
    N = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int32)
    x = np.arange(N, dtype=np.int32)
    a = x // k
    b = x % k
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    B = (b[:, None] + b[None, :]) % k
    return (A * k + B).astype(np.int32)


def _inverse(table):
    """Inverse map of a group table whose identity is element 0."""
    N = table.shape[0]
    inv = np.empty(N, dtype=np.int64)
    rows, cols = np.nonzero(table == 0)
    inv[rows] = cols
    return inv


def _cost(S, table, inv, N):
    """Uncovered elements of (S^-1 S)^2 plus those of (S S^-1)^2; zero iff the Haar graph has diameter <= 5."""
    Sinv = inv[S]
    P = table[Sinv[:, None], S[None, :]].ravel().astype(np.int64)
    PP = table[P[:, None], P[None, :]].ravel().astype(np.int64)
    c1 = N - int(np.count_nonzero(np.bincount(PP, minlength=N)))
    Q = table[S[:, None], Sinv[None, :]].ravel().astype(np.int64)
    QQ = table[Q[:, None], Q[None, :]].ravel().astype(np.int64)
    c2 = N - int(np.count_nonzero(np.bincount(QQ, minlength=N)))
    return c1 + c2


def _anneal(table, inv, N, d, rng, end):
    """Simulated annealing over d-subsets of the group; returns a zero-cost connection set or None."""
    while time.monotonic() < end:
        S = np.array(rng.sample(range(N), d), dtype=np.int64)
        cost = _cost(S, table, inv, N)
        T = 1.0
        for it in range(30000):
            if cost == 0:
                return S
            if (it & 127) == 0 and time.monotonic() >= end:
                return None
            i = rng.randrange(d)
            x = rng.randrange(N)
            if (S == x).any():
                continue
            S2 = S.copy()
            S2[i] = x
            c2 = _cost(S2, table, inv, N)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                S, cost = S2, c2
            T = max(0.2, T * 0.9995)
    return None


def _group_search(d, D, rng, deadline, best):
    """Anneal connection sets over metacyclic groups of increasing order; keep the largest valid Haar graph."""
    moore = lib.moore_bound(d, D)
    N = 2001 if d == 10 else max(d + 1, int(0.27 * moore / 2) + 1)
    best_size = best[0]
    while time.monotonic() < deadline:
        groups = _groups_for(N)
        rng.shuffle(groups)
        for (m, k, r) in groups[:10]:
            if time.monotonic() >= deadline:
                return best
            table = _metacyclic_table(m, k, r)
            inv = _inverse(table)
            slice_end = min(deadline, time.monotonic() + 2.0)
            S = _anneal(table, inv, N, d, rng, slice_end)
            if S is None:
                continue
            us = np.tile(np.arange(N, dtype=np.int64), d)
            vs = table[S].ravel().astype(np.int64) + N
            edges = list(zip(us.tolist(), vs.tolist()))
            n = 2 * N
            if n > best_size and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_size = n
                break
        N += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid

    # Cyclic Haar baseline (short budget).
    cyc_deadline = start + 0.1 * time_limit
    m, misses = d + 1, 0
    while time.monotonic() < cyc_deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= cyc_deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            if found[0] > best[0]:
                best = found
            misses = 0
        else:
            misses += 1
        m += 1

    if D == 5 and d >= 3:
        try:
            best = _group_search(d, D, rng, deadline, best)
        except Exception:
            pass
    return best
