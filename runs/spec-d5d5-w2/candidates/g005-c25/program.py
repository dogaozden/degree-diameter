import math
import random
import time

import lib


MAX_GROUPS = 6       # groups tried per order N in the exact bi-Cayley search
CLIMB_ITERS = 250    # hill-climb steps per group
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# D = 3 baseline: projective plane incidence graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k (exact hill-climb), then a different step:
# take the lowest-cost near-miss connection set, turn it into an UNSTRUCTURED
# bipartite graph, and repair the remaining bad pairs with degree-preserving
# double-edge swaps. The symmetry is broken only where it is needed.
# ----------------------------------------------------------------------------

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
    """Count (source, vertex) pairs not within distance D, from A_0 and B_0.

    Bi-Cayley graph: A_x ~ B_{x g} for g in S. Left translation is an automorphism,
    so eccentricities from A_0 and B_0 determine validity for the whole graph.
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


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Hill-climb a connection set S (containing the identity). Returns (S, cost)."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
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
        if v <= cur:
            S, cur = S2, v
    return S, cur


def _repair(N, S, T, D, rng, deadline):
    """Anneal an unstructured d-regular bipartite graph (from a near-miss bi-Cayley set)
    by double-edge swaps that keep every degree fixed, minimising bad pairs.

    Returns the edge list when all pairs are within distance D, else None.
    """
    n = 2 * N
    E = [(x, N + T[x][g]) for x in range(N) for g in S]
    Es = set(E)
    M = len(E)
    cost = lib.bad_pairs(n, E, D)
    temp = 1.0
    while cost > 0 and time.monotonic() < deadline:
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in Es or n2 in Es:
            continue
        E[i] = n1
        E[j] = n2
        c2 = lib.bad_pairs(n, E, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            Es.discard((a1, b1))
            Es.discard((a2, b2))
            Es.add(n1)
            Es.add(n2)
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return E if cost == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (and is optimal for D = 2).
    best = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
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

    # Frontier sweep over the bi-Cayley order N (graph has 2N vertices).
    N = max(best[0] // 2 + 1, d + 1)
    while time.monotonic() < deadline and 2 * N <= moore:
        now = time.monotonic()
        climb_deadline = now + 0.3 * (deadline - now)

        found = None
        near = None   # (cost, S, T) of the best near-miss at this order
        groups = _groups(N)
        rng.shuffle(groups)
        for m, k2, r in groups[:MAX_GROUPS]:
            if time.monotonic() > climb_deadline:
                break
            _, _, T, invs = _tables(m, k2, r)
            S, cur = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, climb_deadline)
            if cur == 0:
                found = (T, S)
                break
            if near is None or cur < near[0]:
                near = (cur, S, T)

        if found is not None:
            T, S = found
            E = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, E)
            N += 1
            continue

        if near is None:
            break

        # Different step: repair the near-miss as an unstructured graph.
        _, S, T = near
        E = _repair(N, S, T, D, rng, deadline)
        if E is not None:
            consider(2 * N, E)
            N += 1
            continue
        break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
