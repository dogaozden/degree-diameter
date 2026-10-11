import math
import random
import time

import numpy as np

import lib

# Bi-Cayley lifts over semidirect products Z_m x|_r Z_k, searched by numpy-vectorised
# simulated annealing on the number of vertex pairs at distance > D.
# Safe fallback: K_{d,d}. Every candidate is re-checked by lib.is_valid before it is kept.

MAX_GROUPS = 6
SA_ITERS = 2500
STEP_CAP = 32
_TCACHE = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving groups Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(m, k, r):
    """Cached (order, TT, invs): TT[g][x] = x*g (contiguous columns), invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TCACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = np.array([[mul(x, g) for g in range(order)] for x in range(order)], dtype=np.int64)
    TT = np.ascontiguousarray(T.T)
    invs = [inv(g) for g in range(order)]
    val = (order, TT, invs)
    if len(_TCACHE) >= 24:
        _TCACHE.clear()
    _TCACHE[key] = val
    return val


def _cost(N, TT, invs, S, D):
    """Unreached (source, vertex) pairs from A_0 and B_0 in the bi-Cayley graph A_x ~ B_{xg}, g in S.

    Left translation is an automorphism, so these two sources cover all pairs.
    """
    cf = [TT[g] for g in S]
    cb = [TT[invs[g]] for g in S]
    total = 0
    for side in (0, 1):
        seenA = np.zeros(N, dtype=bool)
        seenB = np.zeros(N, dtype=bool)
        fA = np.zeros(N, dtype=bool)
        fB = np.zeros(N, dtype=bool)
        if side == 0:
            seenA[0] = True
            fA[0] = True
        else:
            seenB[0] = True
            fB[0] = True
        for _ in range(D):
            nb = np.zeros(N, dtype=bool)
            na = np.zeros(N, dtype=bool)
            for c in cf:
                nb[c] |= fA
            for c in cb:
                na[c] |= fB
            nb &= ~seenB
            na &= ~seenA
            seenB |= nb
            seenA |= na
            fA, fB = na, nb
            if not (fA.any() or fB.any()):
                break
        total += 2 * N - int(seenA.sum()) - int(seenB.sum())
    return total


def _search_group(N, TT, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {identity} + (d-1) other elements; returns S with zero cost or None."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cost(N, TT, invs, S, D)
    T0, T1 = 2.0, 0.05
    for it in range(iters):
        if cur == 0:
            break
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        temp = T0 * (T1 / T0) ** (it / max(1, iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _cost(N, TT, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    """Try several groups of order N; return a valid (n, edges) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        order, TT, invs = _table(m, k, r)
        S = _search_group(order, TT, invs, d, D, rng, SA_ITERS, deadline)
        if S is None:
            continue
        edges = [(x, order + int(TT[g][x])) for x in range(order) for g in S]
        n = 2 * order
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1:
        return 1, []
    if D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is d-regular bipartite.
    fallback = lib.haar_graph(d, range(d))
    if D == 2 or d == 1:
        return fallback

    moore = lib._moore_bound(d, D)
    max_N = moore // 2
    rng = random.Random(seed * 1000003 + d * 101 + D)

    best = fallback
    lo = 0  # largest order N that succeeded
    N_low = max(d, moore // 8)
    N = min(N_low, max_N)
    step = max(1, moore // 40)

    while time.monotonic() < deadline and N >= d and N <= max_N:
        res = _attempt(N, d, D, rng, deadline)
        if res is not None:
            lo = N
            n, edges = res
            if n > best[0]:
                best = (n, edges)
            step = min(max(1, step) * 2, STEP_CAP)
            if lo >= max_N:
                break
            N = min(lo + step, max_N)
        else:
            if lo == 0:
                # Nothing found yet: go down, and keep retrying the same order once it is small.
                N = max(d, N - max(1, N // 4))
            else:
                step = max(1, step // 2)
                N = min(lo + step, max_N)
                if N <= lo:
                    N = min(lo + 1, max_N)
            if N == lo and lo >= max_N:
                break

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
