import math
import random
import time

import numpy as np

import lib

TARGET_LO = {10: 2001}   # smallest group orders worth trying (record 4000 = 2 * 2000)
SLICE = 4.0              # seconds of annealing per candidate group


def _cyclic_search(d, D, rng, deadline, best):
    """Random cyclic Haar graphs (the parent's search), used as a fallback."""
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


def _table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k (element (a, b) coded a*k+b), plus inverses."""
    N = m * k
    pw = [pow(r, b, m) for b in range(k)]
    Y = np.arange(N, dtype=np.int64)
    c = Y // k
    dd = Y % k
    mul = np.empty((N, N), dtype=np.int32)
    for x in range(N):
        a, b = divmod(x, k)
        mul[x] = ((a + pw[b] * c) % m) * k + (b + dd) % k
    inv = np.argmax(mul == 0, axis=1).astype(np.int64)
    return mul, inv


def _cost(mul, inv, S, N):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2; the Haar graph has diameter <= 5 iff cost is 0."""
    Si = inv[S]
    t1 = np.unique(mul[Si[:, None], S[None, :]].astype(np.int64).ravel())
    q1 = mul[t1[:, None], t1[None, :]].ravel()
    mk = np.zeros(N, dtype=bool)
    mk[q1] = True
    c1 = N - int(mk.sum())
    t2 = np.unique(mul[S[:, None], Si[None, :]].astype(np.int64).ravel())
    q2 = mul[t2[:, None], t2[None, :]].ravel()
    mk = np.zeros(N, dtype=bool)
    mk[q2] = True
    c2 = N - int(mk.sum())
    return c1 + c2


def _anneal(mul, inv, N, d, rng, t_end):
    """Simulated annealing over connection sets S of size d; returns a zero-cost S or None."""
    S = rng.sample(range(N), d)
    cur = _cost(mul, inv, np.array(S, dtype=np.int64), N)
    if cur == 0:
        return S
    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    frac = 0.0
    it = 0
    while True:
        it += 1
        if it & 63 == 0:
            now = time.monotonic()
            if now >= t_end:
                return None
            frac = (now - t0) / span
        T = 0.8 * (1.0 - frac) + 0.03
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _cost(mul, inv, np.array(S2, dtype=np.int64), N)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S, cur = S2, c2
            if cur == 0:
                return S


def _haar_edges(mul, N, S):
    """Haar graph: A-vertex g joined to B-vertex N + s*g for each s in S."""
    edges = []
    gs = range(N)
    for s in S:
        row = mul[s].tolist()
        for g in gs:
            edges.append((g, N + row[g]))
    return 2 * N, edges


def _order_search(d, D, rng, end, best):
    """Anneal over non-abelian groups Z_m x|_r Z_k with order above the current best half-size."""
    best_n = best[0]
    lo = max(TARGET_LO.get(d, 0), best_n // 2 + 1)
    cands = []
    for N in range(lo, lo + 200):
        for k in range(2, 13):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    cands.append((N, m, k, r))
    rng.shuffle(cands)
    cands = cands[:400]
    for N, m, k, r in cands:
        if time.monotonic() >= end - 0.5:
            break
        if N <= best_n // 2:
            continue
        slice_end = min(end, time.monotonic() + SLICE)
        mul, inv = _table(m, k, r)
        S = _anneal(mul, inv, N, d, rng, slice_end)
        if S is not None:
            n, edges = _haar_edges(mul, N, S)
            if n > best_n and lib.is_valid(n, edges, d, D):
                best, best_n = (n, edges), n
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
    if D != 5 or d < 3:
        return _cyclic_search(d, D, rng, end, best)
    p1_end = start + 0.15 * (end - start)
    best = _cyclic_search(d, D, rng, p1_end, best)
    try:
        best = _order_search(d, D, rng, end, best)
    except Exception:
        pass
    return best
