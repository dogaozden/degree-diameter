import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Search family: bi-Cayley lifts over semidirect products Z_m x|_r Z_k.
#
# A lift on a group G of order N has vertices A_x and B_y (x, y in G), with
# A_x adjacent to B_{x*g} for each g in S, |S| = d. Left translation is an
# automorphism, so the diameter is decided by distances from A_e and B_e.
#
# Search: simulated annealing over the connection set S, minimising the number
# of vertex pairs at distance > D from those two representatives.
# ----------------------------------------------------------------------------

MAX_GROUPS = 6        # groups tried per order N
ANNEAL_ITERS = 1500   # annealing steps per (N, group)
N_WINDOW = 6          # candidate orders above the current lower bound
TABLE_CACHE_LIMIT = 24

_TABLE_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N giving Z_m x|_r Z_k."""
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
    """Cached (order, T, invs): T[x][g] = x*g, invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, T, invs)
    if len(_TABLE_CACHE) >= TABLE_CACHE_LIMIT:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Number of (representative, vertex) pairs not within distance D.

    Representatives are A_e (index 0) and B_e (index N).
    Neighbours: A_x -> B_{x g} (g in S); B_y -> A_{y g^-1}.
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


def _anneal_connection_set(N, T, invs, d, D, rng, deadline, iters):
    """Anneal a connection set S of d distinct group elements to zero unreached pairs."""
    S = rng.sample(range(N), d)
    cur = _unreached(N, T, invs, S, D)
    temp = 2.0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        c = rng.randrange(N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
        temp = max(0.3, temp * 0.998)
    return S if cur == 0 else None


def _search_order(N, d, D, rng, deadline):
    """Try several groups of order N; return (T, S) for the first valid lift, else None."""
    if N < d:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, T, invs = _tables(m, k, r)
        S = _anneal_connection_set(N, T, invs, d, D, rng, deadline, ANNEAL_ITERS)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Structured baselines (used for D = 3 and as seeds).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite with degree d.
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

    # Main search: bi-Cayley lifts with orders just above the current record.
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(N_WINDOW)
        if 2 * N > moore:
            N = moore // 2
        res = _search_order(N, d, D, rng, deadline)
        if res is not None:
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
