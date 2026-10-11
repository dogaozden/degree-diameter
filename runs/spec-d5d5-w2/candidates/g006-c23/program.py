import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x|_r Z_k, one base vertex per side.
# Vertices A_x and B_y (x, y in the group). Edge A_x ~ B_{x*g} for g in S,
# so the graph is bipartite and d-regular with 2N vertices.
#
# Search: simulated annealing over the connection set S (identity fixed as one
# dart, WLOG), with the acceptance threshold drawn before each evaluation so
# that the BFS can exit early. Orders N are swept upward from the current best.
# ----------------------------------------------------------------------------

MAX_GROUPS = 12       # groups tried per order N
ANNEAL_ITERS = 2500   # annealing steps per attempt
RESTARTS = 2          # annealing attempts per group
N_WINDOW = 8          # candidate orders above the current lower bound
N_CAP = 1200          # cap on group order (keeps multiplication tables small)
_BIG = 10 ** 9
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
    """Cached (order, mul, T, invs): T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 24:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D, limit=_BIG):
    """Number of vertices not within distance D, summed over sources A_0 and B_0.

    Left translation is an automorphism of a bi-Cayley graph, so two sources
    suffice. Exits early once the running total exceeds `limit`; any value
    above `limit` means the candidate is rejected.
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
        if total > limit:
            return total
    return total


def _anneal_S(N, T, invs, d, D, rng, iters, deadline):
    """Anneal a connection set S of size d (containing 0) to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    temp0, temp1 = 1.5, 0.15
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = temp0 * (temp1 / temp0) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        # Pre-draw the Metropolis threshold so the BFS can stop early.
        thr = -temp * math.log(1.0 - rng.random())
        old = S[i]
        S[i] = c
        v = _unreached(N, T, invs, S, D, limit=cur + thr)
        if v <= cur + thr:
            cur = v
        else:
            S[i] = old
    return S if cur == 0 else None


def _search_order(N, d, D, rng, deadline):
    """Try several groups of order N; return (T, S) for the first valid lift, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k2, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, _, T, invs = _tables(m, k2, r)
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                break
            S = _anneal_S(N, T, invs, d, D, rng, ANNEAL_ITERS, deadline)
            if S is not None:
                return T, S
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

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

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Projective-plane baseline for D = 3.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: sweep orders N just above the current record.
    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > moore // 2 or lo > N_CAP:
            break
        N = lo + rng.randrange(N_WINDOW)
        if N < d + 1:
            N = d + 1
        if N > N_CAP:
            break
        res = _search_order(N, d, D, rng, deadline)
        if res is not None:
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
