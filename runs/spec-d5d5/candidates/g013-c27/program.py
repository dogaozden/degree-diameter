import math
import random
import time

import lib

_TABLE_CACHE = {}
SAMPLE = 14          # random single-element moves scored per tabu iteration
TENURE = 7           # iterations a removed group element stays forbidden
RESTART_ITERS = 1500  # tabu iterations before a fresh random start


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


def _table(m, k, r):
    """Cached (order, T, invs): T[x][g] = x*g and invs[g] = g^-1 in Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, T, invs)
    if len(_TABLE_CACHE) >= 24:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Number of ordered (source, target) pairs at distance > D from A_0 or B_0.

    Bi-Cayley graph: A_x ~ B_{x g} for g in S. Left translation is an automorphism
    that fixes the sides, so eccentricities of A_0 and B_0 decide the diameter.
    """
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


def _tabu(N, T, invs, d, D, rng, deadline):
    """Tabu search over connection sets S (identity fixed as one dart, WLOG).

    Each step scores a random sample of single-element replacements and takes the
    best non-tabu one (aspiration allowed). Returns a valid S or None.
    """
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_S, best_v = list(S), cur
    tabu = {}
    for it in range(1, RESTART_ITERS + 1):
        if best_v == 0 or time.monotonic() > deadline:
            break
        inS = set(S)
        mv = None
        for _ in range(SAMPLE):
            i = rng.randrange(1, d)
            c = rng.randrange(1, N)
            if c in inS:
                continue
            old = S[i]
            S[i] = c
            v = _unreached(N, T, invs, S, D)
            S[i] = old
            if tabu.get(c, 0) > it and v >= best_v:
                continue
            if mv is None or v < mv[2] or (v == mv[2] and rng.random() < 0.5):
                mv = (i, c, v, old)
        if mv is None:
            continue
        i, c, v, old = mv
        S[i] = c
        tabu[old] = it + TENURE
        if v < best_v:
            best_v = v
            best_S = list(S)
    return best_S if best_v == 0 else None


def _search(d, D, deadline, rng, best, moore):
    """Grow the Bi-Cayley order N upward, one level at a time, while time allows."""
    N = best[0] // 2 + 1
    while 2 * N <= moore and time.monotonic() < deadline:
        now = time.monotonic()
        slice_end = min(deadline, now + max(3.0, 0.35 * (deadline - now)))
        if N < d:
            break
        groups = _groups(N)
        if not groups:
            break
        rng.shuffle(groups)
        found = None
        gi = 0
        while found is None and time.monotonic() < slice_end:
            m, k, r = groups[gi % len(groups)]
            gi += 1
            try:
                _, T, invs = _table(m, k, r)
            except ValueError:
                continue
            S = _tabu(N, T, invs, d, D, rng, slice_end)
            if S is not None:
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                if lib.is_valid(2 * N, edges, d, D):
                    found = (2 * N, edges)
        if found is None:
            break
        best = found
        N = best[0] // 2 + 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} meets the bound 2d

    # Structured record for D = 3 when d - 1 is a prime power (instant).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    best = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)

    try:
        best = _search(d, D, deadline, rng, best, moore)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
