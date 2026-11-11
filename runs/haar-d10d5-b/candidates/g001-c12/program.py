import math
import random
import time
from math import gcd

import numpy as np

import lib

_NMAX = 2400  # largest group order searched (memory and time limit)


def _legacy_build(d, D, seed, time_limit):
    """Parent's cyclic Haar-graph search, kept as the safe fallback."""
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
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


# ---------------------------------------------------------------------------
# Haar graphs over non-abelian metacyclic groups Z_m x| Z_k.
# Vertices A_g = g, B_g = N + g; edges A_g ~ B_{s*g} for s in S.
# Diameter <= 5 holds iff (S^-1 S)^2 = G and (S S^-1)^2 = G, so the search
# drives the number of uncovered group elements to zero.
# ---------------------------------------------------------------------------

def _candidates(N):
    """Return (m, k, r) triples giving non-abelian groups of order N = m*k."""
    out = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        rs = [r for r in range(2, m) if gcd(r, m) == 1 and pow(r, k, m) == 1]
        out.extend((m, k, r) for r in rs[:8])
    return out


def _next_valid(N):
    while N <= _NMAX and not _candidates(N):
        N += 1
    return N


def _group(m, k, r):
    """Multiplication table M[x, y] = x*y and inverse array for Z_m x| Z_k, element (a, b) coded a*k+b."""
    N = m * k
    X = np.arange(N, dtype=np.int32)
    a = X // k
    b = X % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int32)
    M = (((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k
         + (b[:, None] + b[None, :]) % k).astype(np.int32)
    INV = np.argmax(M == 0, axis=1).astype(np.int32)
    return N, M, INV


def _cost(S, N, M, INV):
    """Number of group elements missed by (S^-1 S)^2 plus those missed by (S S^-1)^2."""
    Si = INV[S]
    A1 = M[Si[:, None], S[None, :]].ravel()
    A2 = M[A1[:, None], A1[None, :]].ravel()
    mk = np.zeros(N, dtype=bool)
    mk[A2] = True
    c = N - int(np.count_nonzero(mk))
    B1 = M[S[:, None], Si[None, :]].ravel()
    B2 = M[B1[:, None], B1[None, :]].ravel()
    mk2 = np.zeros(N, dtype=bool)
    mk2[B2] = True
    return c + N - int(np.count_nonzero(mk2))


def _anneal(d, N, M, INV, rng, deadline):
    """Simulated annealing with restarts over connection sets S containing the identity 0."""
    iters = 8000
    while time.monotonic() < deadline:
        Sl = [0] + rng.sample(range(1, N), d - 1)
        S = np.array(Sl, dtype=np.int32)
        cur = _cost(S, N, M, INV)
        for it in range(iters):
            if cur == 0:
                return S
            if (it & 127) == 0 and time.monotonic() >= deadline:
                return None
            T = 1.5 * (1.0 - it / iters) + 0.05
            p = rng.randrange(1, d)
            t = rng.randrange(1, N)
            if t in Sl:
                continue
            new = Sl.copy()
            new[p] = t
            Snew = np.array(new, dtype=np.int32)
            c = _cost(Snew, N, M, INV)
            if c <= cur or rng.random() < math.exp(-(c - cur) / T):
                Sl, S, cur = new, Snew, c
        if cur == 0:
            return S
    return None


def _try(d, N, rng, budget_end, probe_cap):
    """Try to find a valid S for some non-abelian group of order N. Returns (m, k, r, S) or None."""
    gl = _candidates(N)
    rng.shuffle(gl)
    gl = gl[:4]
    t0 = time.monotonic()
    for i, (m, k, r) in enumerate(gl):
        now = time.monotonic()
        if now >= budget_end:
            return None
        sub = min(budget_end, now + max(0.2, (t0 + probe_cap - now) / (len(gl) - i)))
        _, M, INV = _group(m, k, r)
        S = _anneal(d, N, M, INV, rng, sub)
        if S is not None:
            return (m, k, r, S)
    return None


def _edges(N, M, S):
    g = np.arange(N, dtype=np.int64)
    edges = []
    for s in S.tolist():
        h = N + M[s].astype(np.int64)
        edges.extend(zip(g.tolist(), h.tolist()))
    return 2 * N, edges


def _build_d5(d, seed, start, time_limit):
    budget_end = start + max(0.5, 0.75 * time_limit - 2.0)
    rng = random.Random(seed * 7919 + 17)
    budget = budget_end - time.monotonic()
    probe_cap = max(1.0, 0.12 * budget)
    ok = []
    lo, hi = 200, None
    while time.monotonic() < budget_end:
        if hi is None:
            target = int(lo * 1.03) + 1
        else:
            if hi - lo <= max(2, 0.005 * lo):
                break
            target = (lo + hi) // 2
        t = _next_valid(target)
        if t > _NMAX or (hi is not None and t >= hi):
            break
        res = _try(d, t, rng, budget_end, probe_cap)
        if res is not None:
            ok.append((t,) + res)
            lo = t
        else:
            hi = t
    ok.sort(key=lambda x: x[0], reverse=True)
    for N, m, k, r, S in ok:
        Nn, M, _ = _group(m, k, r)
        n, edges = _edges(Nn, M, S)
        if lib.is_valid(n, edges, d, 5):
            return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if D == 5 and d >= 3:
        try:
            res = _build_d5(d, seed, start, time_limit)
        except Exception:
            res = None
        if res is not None:
            return res
    remaining = time_limit - (time.monotonic() - start)
    return _legacy_build(d, D, seed, max(0.5, remaining))
