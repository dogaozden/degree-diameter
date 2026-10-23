import math
import random
import time
from math import gcd

import numpy as np
import lib


def _semidirect_tables(m, k, r):
    """Multiplication and inverse tables for Z_m x|_r Z_k, element (a, b) coded as a*k+b."""
    N = m * k
    X = np.arange(N, dtype=np.int64)
    a = X // k
    b = X % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    A, B = a[:, None], b[:, None]
    C, E = a[None, :], b[None, :]
    mul = ((A + pw[B] * C) % m) * k + (B + E) % k
    nb = (-b) % k
    inv = ((-pw[nb] * a) % m) * k + nb
    return mul.astype(np.int64), inv.astype(np.int64)


def _haar_edges(N, mul, S, variant):
    """Haar graph: A-vertex g joins B-vertex N + (s*g) for s in S (variant 1 uses g*s)."""
    edges = []
    for s in S:
        s = int(s)
        tgt = mul[s] if variant == 0 else mul[:, s]
        for g in range(N):
            edges.append((g, N + int(tgt[g])))
    return edges


def _cost(S, mul, inv, N):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2; zero iff the Haar graph has diameter <= 5."""
    Si = inv[S]
    T = np.unique(mul[Si[:, None], S[None, :]])
    P = mul[T[:, None], T[None, :]].ravel()
    mk = np.zeros(N, dtype=bool)
    mk[P] = True
    c1 = N - int(np.count_nonzero(mk))
    T2 = np.unique(mul[S[:, None], Si[None, :]])
    P2 = mul[T2[:, None], T2[None, :]].ravel()
    mk2 = np.zeros(N, dtype=bool)
    mk2[P2] = True
    c2 = N - int(np.count_nonzero(mk2))
    return c1 + c2


def _anneal(N, mul, inv, d, rng, deadline):
    """Simulated annealing over connection sets S of size d; returns a zero-cost S or None."""
    while True:
        if time.monotonic() >= deadline:
            return None
        Sl = rng.sample(range(N), d)
        c = _cost(np.array(Sl, dtype=np.int64), mul, inv, N)
        L = 3000
        for step in range(L):
            if c == 0:
                return np.array(Sl, dtype=np.int64)
            if step % 256 == 0 and time.monotonic() >= deadline:
                return None
            T = 2.0 - 1.7 * step / L
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in Sl:
                continue
            Sl2 = Sl[:]
            Sl2[i] = x
            c2 = _cost(np.array(Sl2, dtype=np.int64), mul, inv, N)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                Sl, c = Sl2, c2
        if c == 0:
            return np.array(Sl, dtype=np.int64)


def _try_order(N, d, D, rng, budget, deadline):
    """Try to find a valid Haar graph on 2N vertices; return (n, edges) or None."""
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(2, m):
            if gcd(r, m) == 1 and pow(r, k, m) == 1:
                cands.append((m, k, r))
    rng.shuffle(cands)
    cands = cands[:4]
    if not cands:
        cands = [(N, 1, 1)]
    share = budget / len(cands)
    for (m, k, r) in cands:
        mul, inv = _semidirect_tables(m, k, r)
        dl = min(time.monotonic() + share, deadline)
        S = _anneal(N, mul, inv, d, rng, dl)
        if S is None:
            continue
        for variant in (0, 1):
            edges = _haar_edges(N, mul, S.tolist(), variant)
            if lib.is_valid(2 * N, edges, d, D):
                return 2 * N, edges
    return None


def _cyclic_search(d, D, rng, deadline):
    """Fallback for other diameters: random cyclic Haar graphs (the original approach)."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    rng = random.Random(seed)
    if D != 5 or d < 3:
        return _cyclic_search(d, D, rng, deadline)

    # Binary search on the group order N (graph has 2N vertices), with lo known valid.
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
    bound = 1 + d * (d - 1) + d * (d - 1) ** 3
    lo, hi = d, bound + 1
    SLICE = 5.0
    final = False
    while time.monotonic() < deadline:
        if hi - lo <= 1:
            if final or lo + 1 > bound:
                break
            final = True
            N = lo + 1
            budget = deadline - time.monotonic()
        else:
            N = (lo + hi) // 2
            budget = min(SLICE, deadline - time.monotonic())
        if budget <= 0:
            break
        res = _try_order(N, d, D, rng, budget, deadline)
        if res is not None:
            lo = N
            best = res
        else:
            hi = N
    return best
