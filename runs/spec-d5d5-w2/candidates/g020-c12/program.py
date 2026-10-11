import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy:
#   * D = 3: incidence graph of PG(2, q), q the largest prime power with q+1 <= d.
#   * Otherwise: simulated annealing over bi-Cayley lifts (two base vertices,
#     one per side) on semidirect products Z_m x|_r Z_k of order N, sweeping N
#     upward from the current record. Each lift has 2N vertices. Cost is the
#     number of vertex pairs not within distance D, measured from A_0 and B_0.
#     Left translation is an automorphism of the lift, so these two
#     eccentricity checks cover the whole graph.
#   * Safe fallbacks: K_{d,d} (diameter 2), an even cycle for d = 2, and the
#     result is always re-validated with lib.is_valid before returning.
# ----------------------------------------------------------------------------

MAX_GROUPS = 8        # groups tried per candidate order N
ANNEAL_ITERS = 2500   # annealing steps per (group, N) attempt
N_WINDOW = 6          # candidate orders N in [lo, lo + N_WINDOW)
T_START = 3.0
T_END = 0.3

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


def _table(m, k, r):
    """Cached (order, T, invs) with T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    val = _TABLE_CACHE.get(key)
    if val is None:
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(order)] for x in range(order)]
        invs = [inv(g) for g in range(order)]
        val = (order, T, invs)
        if len(_TABLE_CACHE) >= 32:
            _TABLE_CACHE.clear()
        _TABLE_CACHE[key] = val
    return val


def _cost(N, T, invs, S, D):
    """Number of (source, vertex) pairs not within distance D, sources A_0 and B_0.

    Bi-Cayley graph: A_x ~ B_{x g} for g in S. B_y ~ A_{y h} for h in S^-1.
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


def _anneal(N, T, invs, d, D, rng, deadline):
    """Simulated annealing over connection sets S (identity fixed as S[0]).

    Returns a valid S (cost zero) or None.
    """
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cost(N, T, invs, S, D)
    iters = ANNEAL_ITERS
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _cost(N, T, invs, S2, D)
        delta = v - cur
        temp = T_START * (T_END / T_START) ** (it / iters)
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _search(d, D, N, rng, deadline):
    """Try several groups of order N; return (T, S) for the first valid lift, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, T, invs = _table(m, k, r)
        S = _anneal(N, T, invs, d, D, rng, deadline)
        if S is not None:
            return T, S
    return None


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1:
        return 2, [(0, 1)]
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best
    if d == 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        cyc = [(min(a, b), max(a, b)) for a, b in cyc]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc
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
            if best[0] >= moore:
                return best

    # Main search: bi-Cayley lifts aiming above the current record.
    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(N_WINDOW)
        if N > moore // 2:
            N = lo
        if N < d:
            N = d
        res = _search(d, D, N, rng, deadline)
        if res is not None:
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
