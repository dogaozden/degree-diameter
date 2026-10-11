"""Bi-Cayley lifts over semidirect products Z_m x| Z_k, searched by annealing.

Construction: for a group G of order N, vertices A_x and B_x (x in G), with
A_x ~ B_{x g} for each g in a connection set S of size d. This is a bipartite
d-regular graph on 2N vertices. Left translation is an automorphism, so the
diameter check only needs BFS from A_0 and B_0.

Simulated annealing searches S (identity fixed WLOG) to minimise the number of
pairs at distance > D. The target order N starts just above the current best
and climbs. Fallbacks: K_{d,d} (diameter 2) and PG(2,q) incidence for D = 3.

Untested in this session; every returned graph is checked with lib.is_valid.
"""
import math
import random
import time

import lib


MAX_GROUPS = 6        # groups tried per target order in one round
TEMP0 = 2.0           # starting annealing temperature
TEMP_MIN = 0.3
COOL = 0.9995


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N for Z_m x|_r Z_k.

    Non-abelian choices (k > 1 and r != 1) are returned first, shuffled within
    each class by the caller.
    """
    nonab, ab = [], []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                (nonab if (k > 1 and r != 1 % m) else ab).append((m, k, r))
    return nonab, ab


def _tables(m, k, r):
    """(T, invs) with T[x][g] = x*g and invs[g] = g^-1 for the semidirect group."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    return T, invs


def _unreached(N, T, invs, S, D):
    """Pairs (source, vertex) not within distance D, for sources A_0 and B_0."""
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


def _anneal(N, T, invs, d, D, rng, end):
    """Anneal a connection set S of size d (containing identity) to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    temp = TEMP0
    it = 0
    while cur > 0:
        if (it & 15) == 0 and time.monotonic() > end:
            break
        it += 1
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _unreached(N, T, invs, S, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = v
        else:
            S[i] = old
        temp = max(TEMP_MIN, temp * COOL)
    return S if cur == 0 else None


def _search_order(N, d, D, rng, end):
    """Try groups of order N until one yields a valid connection set; return (N, edges) or None."""
    nonab, ab = _groups(N)
    rng.shuffle(nonab)
    rng.shuffle(ab)
    cands = (nonab + ab)[:MAX_GROUPS]
    for m, k, r in cands:
        if time.monotonic() > end:
            break
        T, invs = _tables(m, k, r)
        S = _anneal(N, T, invs, d, D, rng, end)
        if S is not None:
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            return 2 * N, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d < 3:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Projective plane incidence for D = 3 (Heawood graph when d = 3).
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break

    # Main search: bi-Cayley lifts with the target order just above the current best.
    while best[0] < moore and time.monotonic() < deadline:
        N = best[0] // 2 + 1
        if 2 * N > moore:
            break
        remaining = deadline - time.monotonic()
        end = time.monotonic() + max(1.5, 0.2 * remaining)
        end = min(end, deadline)
        res = _search_order(N, d, D, rng, end)
        if res is not None:
            consider(*res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
