import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Strategy:
#   1. Safe fallback K_{d,d} (diameter 2, valid for every d >= 1).
#   2. D = 3: incidence graph of PG(2, q) when q + 1 = d is a prime power.
#   3. NEW: direct simulated annealing over bipartite d-regular graphs. Moves
#      are edge switches (they preserve bipartiteness and degrees). The cost is
#      the number of ordered vertex pairs at distance > D, computed with packed
#      uint64 bitsets. A bisection over the side size N finds the largest
#      feasible N in this family.
#   4. Bi-Cayley lifts over Z_m x|_r Z_k with hill climbing, sweeping upward
#      from the current best order.
# Every candidate is checked with lib.is_valid before it replaces the best.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Edge-switch annealing on bipartite d-regular graphs with N + N vertices.
# ----------------------------------------------------------------------------

def _cost_bits(N, d, D, EL, ER):
    """Ordered vertex pairs not within distance D. Zero means the graph has diameter <= D.

    EL holds left indices 0..N-1, ER holds global right indices N..2N-1.
    """
    V = 2 * N
    el = np.asarray(EL, dtype=np.int64)
    er = np.asarray(ER, dtype=np.int64)
    oL = np.argsort(el, kind="stable")
    oR = np.argsort(er, kind="stable")
    nbr = np.empty((V, d), dtype=np.int64)
    nbr[:N] = er[oL].reshape(N, d)   # each left vertex has exactly d neighbours
    nbr[N:] = el[oR].reshape(N, d)   # each right vertex has exactly d neighbours
    W = (V + 63) // 64
    reach = np.zeros((V, W), dtype=np.uint64)
    idx = np.arange(V)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        reach = reach | np.bitwise_or.reduce(reach[nbr], axis=1)
    total = int(_POP8[reach.view(np.uint8)].sum())
    return V * V - total


def _anneal(N, d, D, rng, deadline):
    """Anneal an N+N bipartite d-regular graph to diameter <= D. Returns (EL, ER) or None."""
    if N < d:
        return None
    V = 2 * N
    EL, ER = [], []
    for k in range(d):                      # circulant start: simple and d-regular
        for i in range(N):
            EL.append(i)
            ER.append(N + (i + k) % N)
    M = len(EL)
    edset = {a * V + b for a, b in zip(EL, ER)}
    cost = _cost_bits(N, d, D, EL, ER)
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    T0, T1 = 1.5, 0.05
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t_start) / span
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(M)
        j = rng.randrange(M)
        a, b = EL[i], ER[i]
        c, e = EL[j], ER[j]
        if a == c or b == e:
            continue
        k1 = a * V + e
        k2 = c * V + b
        if k1 in edset or k2 in edset:
            continue
        EL[i], ER[i] = a, e
        EL[j], ER[j] = c, b
        new = _cost_bits(N, d, D, EL, ER)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
            edset.discard(a * V + b)
            edset.discard(c * V + e)
            edset.add(k1)
            edset.add(k2)
        else:
            EL[i], ER[i] = a, b
            EL[j], ER[j] = c, e
    if cost == 0:
        return EL, ER
    return None


def _bisect_anneal(d, D, moore, rng, deadline):
    """Bisect over the side size N; return (N, EL, ER) for the largest feasible N found."""
    lo = d                       # K_{d,d} (N = d) is feasible for D >= 2
    best = None
    hi = max(lo, moore // 2)
    while lo < hi and time.monotonic() < deadline:
        mid = (lo + hi + 1) // 2
        now = time.monotonic()
        share = max(1.0, (deadline - now) * 0.5)
        res = _anneal(mid, d, D, rng, now + share)
        if res is not None:
            lo = mid
            best = res
        else:
            hi = mid - 1
    if best is None:
        return None
    return lo, best[0], best[1]


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k (one base vertex per side).
# ----------------------------------------------------------------------------

MAX_GROUPS = 12
CLIMB_ITERS = 1500
STALL_LIMIT = 300
N_WINDOW = 8
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
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k."""
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
    """Pairs not within distance D, counted from A_0 and B_0 (enough by transitivity)."""
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
        if v < cur:
            stall = 0
        else:
            stall += 1
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

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every d >= 1.
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

    if best[0] >= moore:
        return best

    # Phase 1 (new): bisection over edge-switch annealing.
    phase1_deadline = start + 0.4 * budget
    res = _bisect_anneal(d, D, moore, rng, phase1_deadline)
    if res is not None:
        N, EL, ER = res
        edges = list(zip(EL, ER))
        consider(2 * N, edges)

    # Phase 2: bi-Cayley lifts, sweeping upward from the current best order.
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(N_WINDOW)
        res2 = _search_bicayley(d, D, N, rng, deadline)
        if res2 is not None:
            T, S = res2
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
