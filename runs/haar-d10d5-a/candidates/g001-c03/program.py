import math
import random
import time
from math import isqrt

import numpy as np

import lib


# ---------------------------------------------------------------- cyclic baseline (parent's search)

def _cyclic(d, D, rng, deadline, best):
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


# ---------------------------------------------------------------- metacyclic groups Z_m x| Z_k

def _divisors(n):
    small, large = [], []
    for i in range(1, isqrt(n) + 1):
        if n % i == 0:
            small.append(i)
            if i != n // i:
                large.append(n // i)
    return small + large


def _params(N, rng):
    """Nonabelian semidirect Z_m x| Z_k of order N: (m, k, r) with r != 1, gcd(r, m) = 1, r^k = 1 mod m."""
    out = []
    for k in _divisors(N):
        if k < 2:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    rng.shuffle(out)
    return out[:6]


def _tables(m, k, r):
    """Vectorised multiplication and inverse tables of the group coded as a*k+b (same law as lib.semidirect_group)."""
    N = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    a, b = x // k, x % k
    A, B = a[:, None], b[:, None]
    C, Dd = a[None, :], b[None, :]
    mul = (((A + pw[B] * C) % m) * k + (B + Dd) % k).astype(np.int32)
    nb = (-b) % k
    inv = ((-pw[nb] * a) % m) * k + nb
    return N, mul, inv.astype(np.int64)


# ---------------------------------------------------------------- Haar cost for diameter 5

def _cost(S, mul, inv, N):
    """Uncovered elements in (S^-1 S)^2 plus in (S S^-1)^2. Zero iff the Haar graph has diameter <= 5."""
    iS = inv[S]
    P = np.unique(mul[iS[:, None], S[None, :]])
    mark = np.zeros(N, dtype=bool)
    mark[mul[P[:, None], P[None, :]]] = True
    c1 = N - int(mark.sum())
    Q = np.unique(mul[S[:, None], iS[None, :]])
    mark = np.zeros(N, dtype=bool)
    mark[mul[Q[:, None], Q[None, :]]] = True
    return c1 + N - int(mark.sum())


def _anneal(N, mul, inv, d, rng, deadline, K=6, T=1.2, patience=4000):
    """Best-of-K annealing over connection sets S (identity always included)."""
    def fresh():
        S = np.array([0] + rng.sample(range(1, N), d - 1), dtype=np.int64)
        return S, _cost(S, mul, inv, N)

    S, cur = fresh()
    best_c, best_S = cur, S.copy()
    stall = 0
    while best_c > 0 and time.monotonic() < deadline:
        pick = None
        for _ in range(K):
            i = rng.randrange(1, d)
            new = rng.randrange(1, N)
            if new in S:
                continue
            S2 = S.copy()
            S2[i] = new
            c = _cost(S2, mul, inv, N)
            if pick is None or c < pick[0]:
                pick = (c, S2)
        if pick is None:
            continue
        c, S2 = pick
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            S, cur = S2, c
        if cur < best_c:
            best_c, best_S, stall = cur, S.copy(), 0
        else:
            stall += 1
        if stall > patience:
            S, cur = fresh()
            stall = 0
    return best_c, best_S


def _graph(N, mul, S, d):
    """Haar graph: A-vertex g ~ B-vertex s*g for s in S. Vertex ids: A g = g, B g = N + g."""
    edges = []
    for s in S.tolist():
        row = mul[s].tolist()
        for g in range(N):
            edges.append((g, N + row[g]))
    return 2 * N, edges


def _attempt(N, d, rng, until, params_cache):
    """Try to find S with zero cost in a group of order N, until the given time."""
    if N not in params_cache:
        params_cache[N] = _params(N, rng)
    params = params_cache[N]
    if not params:
        return None
    budget = until - time.monotonic()
    i = 0
    while time.monotonic() < until:
        now = time.monotonic()
        m, k, r = params[i % len(params)]
        i += 1
        slice_end = min(until, now + max(1.0, budget / len(params)))
        _, mul, inv = _tables(m, k, r)
        c, S = _anneal(N, mul, inv, d, rng, slice_end)
        if c == 0:
            return _graph(N, mul, S, d)
    return None


def _nearest(c, L, H, params_cache, rng):
    """Closest N to c in [L, H] that admits a nonabelian metacyclic group."""
    for delta in range(0, H - L + 2):
        for N in (c + delta, c - delta):
            if L <= N <= H:
                if N not in params_cache:
                    params_cache[N] = _params(N, rng)
                if params_cache[N]:
                    return N
    return None


# ---------------------------------------------------------------- main entry point

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + total

    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid

    if D != 5 or d < 3:
        return _cyclic(d, D, rng, deadline, best)

    # Baseline from cyclic Haar graphs (short slice).
    best = _cyclic(d, D, rng, start + 0.12 * total, best)

    # Search non-abelian metacyclic Haar graphs; bisect on the group order N.
    # A Haar graph on G has 2|G| vertices, so we need |G| > best_n / 2.
    successes = []           # (n, edges), unvalidated, ascending in N
    params_cache = {}
    L = best[0] // 2 + 1
    Hmax = max(L, int(lib.moore_bound(d, D) // 2 * 0.4))
    H = Hmax

    while L <= H and time.monotonic() < deadline:
        mid = (L + H) // 2
        N = _nearest(mid, L, H, params_cache, rng)
        if N is None:
            break
        remaining = deadline - time.monotonic()
        budget = min(8.0, max(2.0, remaining / 4))
        res = _attempt(N, d, rng, min(deadline, time.monotonic() + budget), params_cache)
        if res is not None:
            successes.append(res)
            L = N + 1
        else:
            H = N - 1

    # Spend the leftover time on the boundary order just above the best success.
    while time.monotonic() < deadline and L <= Hmax:
        N = _nearest(L, L, Hmax, params_cache, rng)
        if N is None:
            break
        res = _attempt(N, d, rng, deadline, params_cache)
        if res is None:
            break
        successes.append(res)
        L = N + 1

    # Validate the largest candidates first; keep the first that passes.
    for n, edges in reversed(successes):
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return best
