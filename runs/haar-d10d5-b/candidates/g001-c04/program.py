import math
import random
import time

import numpy as np

import lib


def _parent_search(d, D, rng, deadline, best):
    """Cyclic Haar-graph search (the parent's method), keeping the largest valid graph."""
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
            if found[0] > best[0]:
                best = found
            misses = 0
        else:
            misses += 1
        m += 1
    return best


def _table(m, k, r):
    """Multiplication and inverse tables of the metacyclic group Z_m x| Z_k, element (a, b) coded a*k+b."""
    N = m * k
    idx = np.arange(N, dtype=np.int64)
    a = idx // k
    b = idx % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    na = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    nb = (b[:, None] + b[None, :]) % k
    M = (na * k + nb).astype(np.int32)
    I = np.argmax(M == 0, axis=1).astype(np.int64)
    return M, I


def _groups_for(N, rng):
    """Non-abelian metacyclic groups of order N as (m, k, r); falls back to the cyclic group."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m == 1:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    if not out:
        out = [(1, N, 0)]
    rng.shuffle(out)
    return out[:6]


def _cost(S, M, I, N):
    """Number of group elements missed by (S^-1 S)^2 plus those missed by (S S^-1)^2."""
    S = np.asarray(S, dtype=np.int64)
    Si = I[S]
    mark = np.zeros(N, dtype=bool)
    mark[M[Si[:, None], S[None, :]].ravel()] = True
    P = np.flatnonzero(mark)
    mark[:] = False
    mark[M[P[:, None], P[None, :]].ravel()] = True
    c = N - int(mark.sum())
    mark[:] = False
    mark[M[S[:, None], Si[None, :]].ravel()] = True
    P = np.flatnonzero(mark)
    mark[:] = False
    mark[M[P[:, None], P[None, :]].ravel()] = True
    c += N - int(mark.sum())
    return c


def _anneal(M, I, N, d, rng, deadline):
    """Simulated annealing over connection sets S of size d with cost 0 (diameter <= 5 Haar graph)."""
    S = rng.sample(range(N), d)
    c = _cost(S, M, I, N)
    T = 1.5
    while c > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        S2 = list(S)
        S2[i] = x
        c2 = _cost(S2, M, I, N)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = S2, c2
        T = max(0.2, T * 0.999)
    return S if c == 0 else None


def _group_sweep(d, D, rng, deadline, best):
    """Search non-abelian groups for Haar graphs with diameter <= 5; order: just above 2000, then below."""
    order = list(range(2001, 2121)) + list(range(2000, 0, -1))
    for N in order:
        if time.monotonic() >= deadline:
            break
        if N <= best[0] // 2:
            continue
        groups = _groups_for(N, rng)
        if not groups:
            continue
        per = 0.5 / len(groups)
        for (m, k, r) in groups:
            now = time.monotonic()
            if now >= deadline:
                break
            M, I = _table(m, k, r)
            S = _anneal(M, I, N, d, rng, min(deadline, now + per))
            if S is not None:
                edges = []
                for s in S:
                    row = M[s].tolist()
                    edges.extend((g, N + row[g]) for g in range(N))
                n = 2 * N
                if n > best[0] and lib.is_valid(n, edges, d, D):
                    best = (n, edges)
                break
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = 0.8 * time_limit
    deadline = start + budget
    rng = random.Random(seed)

    # Safe fallback: K_{d,d}, always valid for diameter >= 2 with degree d.
    best = lib.haar_graph(d, range(d))

    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    try:
        if D != 5:
            best = _parent_search(d, D, rng, deadline, best)
        else:
            # Baseline from cyclic Haar graphs, then the bold non-abelian group search.
            best = _parent_search(d, D, rng, start + 0.25 * budget, best)
            best = _group_sweep(d, D, rng, deadline, best)
    except Exception:
        pass

    n, edges = best
    if lib.is_valid(n, edges, d, D):
        return n, edges
    fallback = lib.haar_graph(d, range(d))
    return fallback
