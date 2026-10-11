import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane baseline for D = 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW: bit-parallel BFS for cyclic bi-Cayley graphs.
#
# Bi-Cayley graph on Z_N with one vertex per side: A_x ~ B_{x+g} for g in S.
# A set of vertices on one side is stored as an N-bit Python integer, and
# translation by s is a cyclic rotation of the bits. One BFS level costs
# |S| rotations of an N-bit integer, far cheaper than per-vertex Python loops.
# Left translation is an automorphism, so eccentricities of A_0 and B_0
# decide the diameter of the whole graph.
# ----------------------------------------------------------------------------

def _cyc_unreached(N, M, S, negs, D):
    """Count pairs (source, vertex) with distance > D, for sources A_0 and B_0.

    S: connection set (A->B shifts). negs: (-g) mod N for g in S (B->A shifts).
    M: mask with N low bits set. Zero means the bi-Cayley graph has diameter <= D.
    """
    total = 0
    for src in (0, 1):
        vis = [0, 0]
        vis[src] = 1
        side = src
        F = 1
        for _ in range(D):
            shifts = S if side == 0 else negs
            nxt = 0
            for s in shifts:
                if s:
                    nxt |= ((F << s) | (F >> (N - s))) & M
                else:
                    nxt |= F
            other = 1 - side
            nxt &= ~vis[other]
            if not nxt:
                break
            vis[other] |= nxt
            F = nxt
            side = other
        total += 2 * N - vis[0].bit_count() - vis[1].bit_count()
    return total


CYC_STALL = 250


def _cyc_search(N, d, D, rng, deadline):
    """Hill-climb a connection set S in Z_N (0 fixed in S) until the lift has diameter <= D."""
    M = (1 << N) - 1

    def evaluate(S):
        return _cyc_unreached(N, M, S, [(N - g) % N for g in S], D)

    S = [0] + rng.sample(range(1, N), d - 1)
    cur = evaluate(S)
    stall = 0
    while cur and time.monotonic() < deadline:
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = evaluate(S2)
        if v < cur:
            stall = 0
        else:
            stall += 1
        if v <= cur:
            S, cur = S2, v
        if stall > CYC_STALL:
            S = [0] + rng.sample(range(1, N), d - 1)
            cur = evaluate(S)
            stall = 0
    return S if cur == 0 else None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over non-abelian groups Z_m x|_r Z_k (semidirect products).
# ----------------------------------------------------------------------------

MAX_GROUPS = 8
CLIMB_ITERS = 1200
STALL_LIMIT = 250
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
    """Cached (order, mul, T, invs) with T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs at distance > D from A_0 and B_0."""
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


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Hill-climb a connection set S (identity fixed as one dart) to zero unreached pairs."""
    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _unreached(N, T, invs, S, D)

    S, cur = fresh()
    stall = 0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        stall = 0 if v < cur else stall + 1
        if v <= cur:
            S, cur = S2, v
        if stall > STALL_LIMIT:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


def _search_bicayley(d, D, N, rng, deadline):
    """Try several groups of order N; return (T, S) for the first valid lift, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k2, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, _, T, invs = _tables(m, k2, r)
        S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

N_WINDOW = 8        # candidate orders above the current lower bound
CYC_PROB = 0.7      # fraction of attempts using the fast cyclic search


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d == 1:
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

    # Time slice per candidate order: enough for a fast cyclic climb to succeed,
    # short enough to sweep several orders.
    slice_len = max(1.0, budget / 14.0)

    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = max(n_best // 2 + 1, d)
        if lo > moore // 2:
            break
        N = lo + rng.randrange(N_WINDOW)
        slice_end = min(deadline, time.monotonic() + slice_len)

        if rng.random() < CYC_PROB:
            S = _cyc_search(N, d, D, rng, slice_end)
            if S is not None:
                edges = [(x, N + (x + g) % N) for x in range(N) for g in S]
                consider(2 * N, edges)
        else:
            res = _search_bicayley(d, D, N, rng, slice_end)
            if res is not None:
                T, S = res
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
