import math
import random
import time

import numpy as np

import lib


def _cyclic_fallback(d, D, seed, deadline):
    """Parent's search: cyclic Haar graphs with random connection sets."""
    rng = random.Random(seed)
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


def _make_group(m, k, r):
    """Vectorised Z_m x|_r Z_k; element (a, b) is coded as a*k + b (same coding as lib.semidirect_group)."""
    P = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)

    def mul(x, y):
        a, b = np.divmod(x, k)
        c, e = np.divmod(y, k)
        return ((a + P[b] * c) % m) * k + (b + e) % k

    def inv(x):
        a, b = np.divmod(x, k)
        nb = (-b) % k
        return ((-P[nb] * a) % m) * k + nb

    return mul, inv


def _cost(S, mul, inv, N):
    """Number of group elements missed by (S^-1 S)^2 plus those missed by (S S^-1)^2. Zero iff diameter <= 5."""
    Si = inv(S)
    total = 0
    for Z in (mul(Si[:, None], S[None, :]).ravel(), mul(S[:, None], Si[None, :]).ravel()):
        Z = np.unique(Z)
        W = mul(Z[:, None], Z[None, :]).ravel()
        mark = np.zeros(N, dtype=bool)
        mark[W] = True
        total += N - int(mark.sum())
    return total


def _anneal(N, d, mul, inv, rng, t_end):
    """Simulated annealing over connection sets S with 1 in S. Returns a zero-cost S as a list, or None."""
    while time.monotonic() < t_end:
        S = [0] + rng.sample(range(1, N), d - 1)
        cur = _cost(np.array(S, dtype=np.int64), mul, inv, N)
        best_local, stall = cur, 0
        while cur > 0 and stall < 3000:
            if time.monotonic() >= t_end:
                return None
            i = rng.randrange(1, d)
            g = rng.randrange(1, N)
            if g in S:
                continue
            old = S[i]
            S[i] = g
            new = _cost(np.array(S, dtype=np.int64), mul, inv, N)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / 0.6):
                cur = new
            else:
                S[i] = old
            if cur < best_local:
                best_local, stall = cur, 0
            else:
                stall += 1
        if cur == 0:
            return S
    return None


def _candidates(lo, hi, rng):
    """Yield (N, m, k, r) for semidirect groups of order N in [lo, hi], by increasing N."""
    for N in range(lo, hi + 1):
        opts = []
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            if rs:
                rng.shuffle(rs)
                for r in rs[:2]:
                    opts.append((N, m, k, r))
        rng.shuffle(opts)
        yield from opts


def _graph(N, S, mul):
    """Haar-type bipartite graph: A_g = g, B_h = N + h, edge A_g ~ B_{s g} for s in S."""
    G = np.arange(N, dtype=np.int64)
    edges = []
    for s in S:
        h = mul(np.full(N, s, dtype=np.int64), G)
        edges.extend(zip(G.tolist(), (N + h).tolist()))
    return 2 * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget_end = start + 0.72 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    if D != 5 or d < 3:
        return _cyclic_fallback(d, D, seed, start + 0.8 * time_limit)

    # Group-Haar search for diameter 5. Moore-type counting bound on |G|.
    B = 1 + d * (d - 1) + d * (d - 1) ** 3
    lo = max(d + 1, int(0.27 * B))
    hi = int(0.36 * B)
    rng = random.Random(seed)
    SLICE = 2.0

    solutions = []  # (N, S, mul), N increasing
    for N, m, k, r in _candidates(lo, hi, rng):
        now = time.monotonic()
        if now >= budget_end:
            break
        if solutions and N <= solutions[-1][0]:
            continue
        mul, inv = _make_group(m, k, r)
        S = _anneal(N, d, mul, inv, rng, min(budget_end, now + SLICE))
        if S is not None:
            solutions.append((N, S, mul))

    # Verify from the largest solution down; keep the first that passes the exact check.
    for N, S, mul in reversed(solutions):
        n, edges = _graph(N, S, mul)
        if lib.is_valid(n, edges, d, D):
            return n, edges

    return lib.haar_graph(d, range(d))
