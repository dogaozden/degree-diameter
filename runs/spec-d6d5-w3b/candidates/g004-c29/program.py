import math
import random
import time
import itertools

import lib


# ----------------------------------------------------------------------------
# Algebraic baselines (fast, deterministic).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New construction: bi-Cayley graphs over small non-abelian groups.
#
# Group G of order N (semidirect product Z_m x| Z_k), connection set S of size d.
# Vertices: (g, 0) -> id g, and (h, 1) -> id N + h.
# Edges: (g, 0) -- (g*s, 1) for every s in S.
# Left multiplication by any element is an automorphism that preserves the two
# sides, so the diameter condition reduces to two BFS runs, from (e, 0) and
# from (e, 1). The graph is bipartite and d-regular by construction.
# The search hill-climbs over S for a fixed group, then the lift is verified.
# ----------------------------------------------------------------------------

def _group_options(N, cache, kmax=12):
    """All (m, k, r) with m * k = N, k <= kmax, usable for semidirect_group."""
    if N in cache:
        return cache[N]
    opts = []
    for k in range(1, min(kmax, N) + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    cache[N] = opts
    return opts


def _unreached_cost(N, D, perms, invps):
    """Number of (start, vertex) pairs not reached within D from (e,0) and (e,1). Zero means diameter <= D."""
    M = 2 * N
    total = 0
    for start in (0, N):
        seen = bytearray(M)
        seen[start] = 1
        frontier = [start]
        count = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    for p in perms:
                        w = N + p[v]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    h = v - N
                    for ip in invps:
                        w = ip[h]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += M - count
    return total


def _search_cayley(N, d, D, rng, deadline, steps, opt_cache):
    """Hill-climb a connection set S of size d in a random group of order N.

    Returns (mul, S) when the bi-Cayley graph has diameter <= D, else None.
    """
    if N < d:
        return None
    opts = _group_options(N, opt_cache)
    if not opts:
        return None
    m, k, r = rng.choice(opts)
    _, mul, _ = lib.semidirect_group(m, k, r)
    pc = {}

    def perm_pair(s):
        if s not in pc:
            p = [mul(g, s) for g in range(N)]
            ip = [0] * N
            for g, x in enumerate(p):
                ip[x] = g
            pc[s] = (p, ip)
        return pc[s]

    def cost(S):
        pairs = [perm_pair(s) for s in S]
        return _unreached_cost(N, D, [a for a, _ in pairs], [b for _, b in pairs])

    S = rng.sample(range(N), d)
    cur = cost(S)
    for _ in range(steps):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        c = cost(T)
        if c <= cur:
            S, cur = T, c
    if cur != 0:
        return None
    return mul, S


def _cayley_edges(N, mul, S):
    """Edge list of the bi-Cayley graph on 2N vertices."""
    return [(g, N + mul(g, s)) for s in S for g in range(N)]


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    # Algebraic families.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Bi-Cayley search over small semidirect products. Each candidate is checked
    # with two BFS runs, so many candidates fit in the budget.
    moore = lib.moore_bound(d, D)
    half_cap = moore // 2
    opt_cache = {}
    try:
        while time.monotonic() < deadline:
            lo = best_n // 2 + 1
            if lo > half_cap or lo < 2:
                break
            N = rng.randint(lo, lo + 24)
            if N > half_cap:
                N = lo
            res = _search_cayley(N, d, D, rng, deadline, 150, opt_cache)
            if res is not None:
                mul, S = res
                n2 = 2 * N
                e2 = _cayley_edges(N, mul, S)
                consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
