import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cheap families used as the safe fallback.
# ----------------------------------------------------------------------------

def _pg_fallback(d):
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
# New construction: bipartite doubles of Cayley-type graphs over groups.
#
# Group G of order N acts regularly on both sides. Vertices A_g = g and B_h = N + h.
# Connection set S = {s_1..s_d} (distinct group elements) gives edges A_g -- B_{g*s}.
# Each side has degree d. Left translation is an automorphism, so the diameter is
# at most D iff BFS from A_e and from B_e reach every vertex within D steps.
# The search is a simulated annealing over S, with fresh random groups
# (cyclic or semidirect Z_m x| Z_k) whenever a group stalls.
# ----------------------------------------------------------------------------

def _random_group(N, rng):
    """Random group of order N as (order, mul, inv), coded 0..N-1, or None."""
    ks = [k for k in range(1, min(N, 12) + 1) if N % k == 0]
    k = 1 if rng.random() < 0.4 else rng.choice(ks)
    m = N // k
    if m < 2:
        return None
    if k == 1:
        r = 1
    else:
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    order, mul, inv = lib.semidirect_group(m, k, r)
    if order != N:
        return None
    return order, mul, inv


def _unreached(S, N, D, T, invl):
    """Number of (source, vertex) pairs not within distance D; sources are A_e and B_e."""
    V = 2 * N
    adjA = [[N + row[s] for s in S] for row in T]          # A_g -> B_{g s}
    invS = [invl[s] for s in S]
    adjB = [[row[t] for t in invS] for row in T]           # B_h -> A_{h s^-1}
    adj = adjA + adjB
    total = 0
    for src in (0, N):
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += V - cnt
    return total


def _edges(S, N, T):
    return [(g, N + T[g][s]) for g in range(N) for s in S]


def _anneal(d, D, N, T, invl, rng, iters, deadline):
    """Anneal a connection set S of size d in a fixed group. Returns S with zero cost or None."""
    S = rng.sample(range(N), d)
    c = _unreached(S, N, D, T, invl)
    for it in range(iters):
        if c == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _unreached(S2, N, D, T, invl)
        temp = 1.5 * (1.0 - it / iters) + 0.05
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            S, c = S2, c2
    return S if c == 0 else None


def _search(d, D, deadline, rng, N, consider, floor):
    """Climb the group order N while solutions keep being found; back off when stuck."""
    fails = 0
    while time.monotonic() < deadline:
        grp = _random_group(N, rng)
        if grp is None:
            continue
        order, mul, inv = grp
        T = [[mul(g, s) for s in range(N)] for g in range(N)]
        invl = [inv(s) for s in range(N)]
        S = _anneal(d, D, N, T, invl, rng, 800, deadline)
        if S is not None:
            consider(2 * N, _edges(S, N, T))
            floor = N
            fails = 0
            N += max(1, N // 100)
        else:
            fails += 1
            if fails >= 6:
                fails = 0
                if N - max(1, N // 100) >= floor:
                    N -= max(1, N // 100)
    return


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Already optimal (Moore bound reached): return instantly.
    if best_n >= lib.moore_bound(d, D):
        return best

    rng = random.Random(seed * 1000003 + d * 97 + D)
    moore = lib.moore_bound(d, D)
    N0 = max(best_n // 2 + 1, moore // 8, d + 1)
    _search(d, D, deadline, rng, N0, consider, floor=N0)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
