import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# D = 3 baseline: incidence graph of PG(2, q) for the largest prime power q
# with q + 1 <= d (meets the Moore bound when d - 1 is a prime power).
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x|_r Z_k.
#
# A bi-Cayley graph on a group G of order N has parts A = {A_x} and B = {B_y}
# with A_x ~ B_{x g} for every g in S, |S| = d. It has 2N vertices and is
# bipartite and d-regular. Left translation is an automorphism, so the diameter
# check only needs eccentricities from A_0 and B_0.
#
# New in this version: the connection set S is found by TABU SEARCH with
# best-of-sampled-neighbourhood moves, instead of simulated annealing. Each step
# evaluates a batch of single-element replacements, takes the best non-tabu one
# (with aspiration when it beats the global best), and restarts when stalled.
# ----------------------------------------------------------------------------

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
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Number of (source, vertex) pairs not within distance D, sources A_0 and B_0."""
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


def _tabu_search(N, T, invs, d, D, rng, deadline, iters, moves, stall_limit):
    """Tabu search over connection sets S (identity fixed as S[0]).

    Each step samples `moves` single-element replacements, takes the best one that
    is not tabu (or that beats the global best), and applies it. The changed
    position is tabu for a short random tenure. A stalled run restarts from a
    fresh random set. Returns a valid S (zero unreached pairs) or None.
    """
    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _unreached(N, T, invs, S, D)

    S, cur = fresh()
    best_S, best_v = list(S), cur
    tabu = {}
    last_improve = 0

    for it in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        if it - last_improve > stall_limit:
            S, cur = fresh()
            tabu = {}
            last_improve = it
            if cur < best_v:
                best_S, best_v = list(S), cur
            continue

        cand = None
        for _ in range(moves):
            i = rng.randrange(1, d)
            c = rng.randrange(1, N)
            if c in S:
                continue
            S2 = S[:]
            S2[i] = c
            v = _unreached(N, T, invs, S2, D)
            if tabu.get(i, -1) > it and v >= best_v:
                continue
            if cand is None or v < cand[0]:
                cand = (v, i, S2)
        if cand is None:
            continue

        v, i, S2 = cand
        S, cur = S2, v
        tabu[i] = it + 2 + rng.randrange(5)
        if cur < best_v:
            best_S, best_v = list(S), cur
            last_improve = it

    return best_S if best_v == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

TABU_ITERS = 600      # tabu steps per group
TABU_MOVES = 24       # sampled moves per tabu step
TABU_STALL = 150      # steps without improvement before a restart
MAX_GROUPS = 6        # groups tried per order N


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))   # K_{d,d}, diameter 2
    if D == 2 or d <= 2:
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
        if best[0] >= moore:
            return best

    # Main search: bi-Cayley lifts with 2N vertices, aiming above the current best.
    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(8)
        groups = _groups(N)
        rng.shuffle(groups)
        for m, k2, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            _, T, invs = _tables(m, k2, r)
            S = _tabu_search(N, T, invs, d, D, rng, deadline,
                             TABU_ITERS, TABU_MOVES, TABU_STALL)
            if S is not None:
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
