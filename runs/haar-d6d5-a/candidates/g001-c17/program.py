import math
import random
import time

import numpy as np

import lib


def _metacyclic_table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k, element (a, b) coded as a*k + b, identity 0."""
    N = m * k
    el = np.arange(N, dtype=np.int64)
    a = el // k
    b = el % k
    pw = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
    # (a, b) * (c, e) = (a + r^b * c, b + e)
    table = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    return table


def _group_options(N, rng):
    """Metacyclic groups of order N as (m, k, r) triples; cyclic group as fallback."""
    opts = []
    for k in range(2, N // 2 + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) != 1:
                continue
            if pow(r, k, m) != 1 % m:
                continue
            opts.append((m, k, r))
    rng.shuffle(opts)
    opts = opts[:20]
    if not opts:
        opts = [(N, 1, 1)]
    return opts


def _cost(table, inv, N, S):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2; zero iff the Haar graph has diameter <= 5."""
    S = np.array(S, dtype=np.int64)
    iS = inv[S]
    total = 2 * N
    for T in (table[iS[:, None], S[None, :]].ravel(),
              table[S[:, None], iS[None, :]].ravel()):
        T = np.unique(T)
        sq = table[T[:, None], T[None, :]].ravel()
        total -= int(np.count_nonzero(np.bincount(sq, minlength=N)))
    return total


def _anneal(table, inv, N, d, rng, deadline, stall_limit):
    """Simulated annealing over connection sets S of size d; returns a zero-cost S or None."""
    while time.monotonic() < deadline:
        S = rng.sample(range(N), d)
        cur = _cost(table, inv, N, S)
        T = 1.0
        stall = 0
        while cur > 0 and stall < stall_limit and time.monotonic() < deadline:
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in S:
                continue
            cand = S[:]
            cand[i] = x
            c = _cost(table, inv, N, cand)
            if c <= cur or rng.random() < math.exp(-(c - cur) / T):
                S = cand
                stall = 0 if c < cur else stall + 1
                cur = c
            else:
                stall += 1
            T = max(0.2, T * 0.9995)
        if cur == 0:
            return S
    return None


def _haar_from_table(table, N, S):
    """Haar graph: A-vertex g adjacent to B-vertex s*g for s in S; A = g, B = N + g."""
    edges = []
    for s in S:
        row = table[int(s)].tolist()
        for g in range(N):
            edges.append((g, N + int(row[g])))
    return 2 * N, edges


def _try_order(d, D, N, rng, deadline):
    """Search groups of order N for a valid Haar graph; return (n, edges) or None."""
    opts = _group_options(N, rng)
    while time.monotonic() < deadline:
        m, k, r = rng.choice(opts)
        table = _metacyclic_table(m, k, r)
        inv = np.argmax(table == 0, axis=1)
        S = _anneal(table, inv, N, d, rng, deadline, stall_limit=3000)
        if S is not None:
            n, edges = _haar_from_table(table, N, S)
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


def _group_search(d, D, rng, deadline):
    """Ascend through group orders from just above the record threshold; return the largest valid graph."""
    bound = lib.moore_bound(d, D) // 2
    lo = max(d + 1, int(0.44 * bound))
    best = None
    fails = 0
    N = lo
    while N <= bound and fails < 3:
        remaining = deadline - time.monotonic()
        if remaining <= 0.2:
            break
        tN = min(remaining, 6.0)
        res = _try_order(d, D, N, rng, time.monotonic() + tN)
        if res is None:
            fails += 1
        else:
            fails = 0
            best = res
        N += 1
    return best


def _cyclic_search(d, D, seed, deadline, best):
    """Fallback: cyclic Haar graphs with connection sets containing 0."""
    rng = random.Random(seed)
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
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid

    if D == 5 and d >= 3:
        try:
            rng = random.Random(seed)
            found = _group_search(d, D, rng, start + 0.7 * time_limit)
            if found is not None and found[0] > best[0]:
                return found
        except Exception:
            pass

    return _cyclic_search(d, D, seed, start + 0.8 * time_limit, best)
