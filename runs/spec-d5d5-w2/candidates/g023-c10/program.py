import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New family for this island: bi-Cayley lifts A_x ~ B_{x g} (g in S) over
# semidirect products Z_m x|_r Z_k, searched by simulated annealing on the
# number of unreached (source, target) pairs, with a sweep over the group
# order N upward from the current best. Each accepted graph is validated.
# The parent's hill-climb, multi-base annealing, arc extensions and GQ
# baselines are dropped; K_{d,d} and PG(2,q) remain as fallbacks.
# ----------------------------------------------------------------------------

MAX_GROUPS = 6      # groups tried per order N
_TABLE_CACHE = {}
_CACHE_LIMIT = 16


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
    """Cached (order, T, invs): T[x][g] = x*g and invs[g] = g^-1 for the group."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, T, invs)
    if len(_TABLE_CACHE) >= _CACHE_LIMIT:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Pairs (source, target) not within distance D, for sources A_0 and B_0.

    Left translation is an automorphism of the bi-Cayley graph, so two
    eccentricities suffice for the whole graph.
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


def _anneal(N, T, invs, d, D, rng, deadline, iters):
    """Simulated annealing over connection sets S containing the identity (WLOG).

    Returns S with zero unreached pairs, or None.
    """
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    t0, t1 = 3.0, 0.2
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = t0 * (t1 / t0) ** (it / max(1, iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _bicayley_edges(N, T, S):
    """Edges of the bi-Cayley graph: A_x = x, B_y = N + y, A_x ~ B_{x g}."""
    return [(x, N + T[x][g]) for x in range(N) for g in S]


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: bi-Cayley sweep over the group order N (graph has 2N vertices).
    lo = best[0] // 2 + 1
    hi = moore // 2
    slice_len = max(0.5, budget / 40.0)
    while lo <= hi and time.monotonic() < deadline:
        N = lo
        lo += 1
        if N < d:
            continue
        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k2, r in groups[:MAX_GROUPS]:
            now = time.monotonic()
            if now > deadline:
                break
            group_deadline = min(deadline, now + slice_len / MAX_GROUPS * 2)
            order, T, invs = _tables(m, k2, r)
            S = _anneal(N, T, invs, d, D, rng, group_deadline, 1500)
            if S is not None:
                found = (T, S)
                break
        if found is not None:
            T, S = found
            consider(2 * N, _bicayley_edges(N, T, S))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
