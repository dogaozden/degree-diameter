import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structural baseline for D = 3: incidence graph of PG(2, q), diameter 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x|_r Z_k.
#
# Vertices A_x and B_y (x, y in G). Connection set S (|S| = d, 0 in S WLOG):
# A_x ~ B_{x g} for g in S. Left translation is an automorphism that is
# transitive on A and on B, so distances from A_0 and B_0 determine the
# diameter. This family is searched by simulated annealing on S, sweeping the
# group order N upward from the smallest order that could beat the current best.
# ----------------------------------------------------------------------------

MAX_GROUPS = 6        # groups tried per order N
ANNEAL_ITERS = 3000   # annealing steps per group
_TABLE_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Cached (order, T, invs): T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, T, invs)
    if len(_TABLE_CACHE) >= 64:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Number of (source, target) pairs not within distance D, sources A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _anneal_S(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over connection sets S with 0 in S; returns S with zero unreached pairs or None."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / iters) + 0.05
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _bicayley_edges(N, T, S):
    return [(x, N + T[x][g]) for x in range(N) for g in S]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2; for d = 2 use an even cycle of length 2D.
    if d == 2:
        best = lib.haar_graph(max(D, 2), [0, 1])
    else:
        best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 3:
        return best if lib.is_valid(best[0], best[1], d, D) else lib.haar_graph(d, range(d))

    # Sweep N upward from the smallest order that would beat the current best.
    # A found order N gives 2N vertices; the sweep then continues above it.
    N = max(d, best[0] // 2 + 1)
    max_N = moore // 2
    while N <= max_N and time.monotonic() < deadline:
        found = None
        groups = _groups(N)
        rng.shuffle(groups)
        for m, k2, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            order, T, invs = _tables(m, k2, r)
            S = _anneal_S(order, T, invs, d, D, rng, ANNEAL_ITERS, deadline)
            if S is not None:
                found = (order, T, S)
                break
        if found is not None:
            n_, T_, S_ = found
            consider(2 * n_, _bicayley_edges(n_, T_, S_))
            N = max(N + 1, best[0] // 2 + 1)
        else:
            N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
