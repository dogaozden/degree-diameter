import math
import random
import time

import numpy as np

import lib


def _parent(d, D, rng, deadline):
    """Random cyclic Haar search from the parent program. Returns a valid (n, edges)."""
    best = lib.haar_graph(d, range(d))
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


def _semi_table(m, k, r, N):
    """Multiplication table of Z_m x|_r Z_k, element (a, b) coded as a*k+b. Entry [x, y] = x*y."""
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    a, b = x // k, x % k
    M = np.empty((N, N), dtype=np.int32)
    for s in range(0, N, 256):
        e = min(N, s + 256)
        A = (a[s:e, None] + pw[b[s:e, None]] * a[None, :]) % m
        B = (b[s:e, None] + b[None, :]) % k
        M[s:e] = A * k + B
    return M


def _inv_table(m, k, r, N):
    """Inverse of each element of Z_m x|_r Z_k."""
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    a, b = x // k, x % k
    nb = (-b) % k
    return ((-pw[nb] * a) % m) * k + nb


def _group_candidates(lo, hi, rng):
    """Metacyclic groups Z_m x|_r Z_k with orders in [lo, hi], non-abelian (r != 1)."""
    out = []
    for N in range(lo, hi + 1):
        group = []
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            found = []
            if pow(m - 1, k, m) == 1:
                found.append(m - 1)
            tries = 0
            while tries < 60 and len(found) < 2:
                r = rng.randrange(2, m)
                tries += 1
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 and r not in found:
                    found.append(r)
            group += [(N, m, k, r) for r in found]
        rng.shuffle(group)
        out.extend(group)
    return out


def _anneal(N, d, M, inv, rng, stop):
    """Search S (d distinct group elements) with cost 0: (S^-1 S)^2 = G and (S S^-1)^2 = G."""

    def cost(S):
        Si = inv[S]
        T = np.unique(M[Si[:, None], S[None, :]])
        TT = M[T[:, None], T[None, :]].ravel()
        c1 = N - np.count_nonzero(np.bincount(TT, minlength=N))
        U = np.unique(M[S[:, None], Si[None, :]])
        UU = M[U[:, None], U[None, :]].ravel()
        c2 = N - np.count_nonzero(np.bincount(UU, minlength=N))
        return int(c1 + c2)

    S = rng.sample(range(N), d)
    cur = cost(np.array(S, dtype=np.int64))
    best, stall = cur, 0
    temp = 0.6
    while True:
        if cur == 0:
            return S
        if time.monotonic() >= stop:
            return None
        i = rng.randrange(d)
        bc, bS = None, None
        for _ in range(8):
            x = rng.randrange(N)
            if x in S:
                continue
            S2 = S[:]
            S2[i] = x
            c = cost(np.array(S2, dtype=np.int64))
            if bc is None or c < bc:
                bc, bS = c, S2
        if bS is None:
            continue
        if bc <= cur or rng.random() < math.exp(-(bc - cur) / temp):
            S, cur = bS, bc
        if cur < best:
            best, stall = cur, 0
        else:
            stall += 1
        if stall > 2000:
            S = rng.sample(range(N), d)
            cur = cost(np.array(S, dtype=np.int64))
            best, stall = cur, 0


def _graph(N, M, S):
    """Haar graph: A-vertex g is g, B-vertex h is N+h; edge (g, A) ~ (s*g, B) for s in S."""
    edges = []
    for s in S:
        row = M[int(s)].tolist()
        edges.extend((g, N + row[g]) for g in range(N))
    return 2 * N, edges


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    rng = random.Random(seed)
    total = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + total
    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, always valid

    if D != 5 or d < 3:
        g = _parent(d, D, rng, end)
        return g if lib.is_valid(g[0], g[1], d, D) else fallback

    # Phase B first: cyclic fallback (parent's method) so a valid graph is always secured.
    best = _parent(d, D, rng, t0 + 0.2 * total)
    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback

    # Phase A: non-abelian metacyclic Haar graphs, aiming above the cyclic records.
    moore = lib.moore_bound(d, D)
    lo = 2001 if d == 10 else max(d, int(0.135 * moore))
    hi = lo + 600
    cands = _group_candidates(lo, hi, rng)
    bestN = best[0] // 2

    for (N, m, k, r) in cands:
        if time.monotonic() >= end:
            break
        if N <= bestN:
            continue
        M = _semi_table(m, k, r, N)
        inv = _inv_table(m, k, r, N)
        stop = min(end, time.monotonic() + 3.5)
        S = _anneal(N, d, M, inv, rng, stop)
        if S is None:
            continue
        n, edges = _graph(N, M, S)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            bestN = N

    n, edges = best
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return fallback
