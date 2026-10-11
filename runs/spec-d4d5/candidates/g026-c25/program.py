import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bipartite Haar graphs over finite groups.
#
# Vertices a_g = g and b_h = N + h for g, h in G (|G| = N). The connection set
# S (|S| = d) gives edges a_g -- b_{g*s} for s in S. Left multiplication by any
# group element is an automorphism, so distances need only be measured from
# a_1 and b_1. The search below is a simulated annealing over S, run on many
# groups of order N close to the Moore limit. The groups are semidirect
# products Z_m x| Z_k, which include cyclic and abelian products.
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _groups_of_order(N):
    """Parameter triples (m, k, r) for semidirect products Z_m x| Z_k of order N."""
    out = [(N, 1, 1)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(m, k, r):
    """Return (N, T, inv) with T[x][y] the product and inv[x] the inverse."""
    N, mul, inv_f = lib.semidirect_group(m, k, r)
    T = [[mul(x, y) for y in range(N)] for x in range(N)]
    inv = [inv_f(x) for x in range(N)]
    return N, T, inv


def _cost(N, T, inv, S, D):
    """Number of (root, vertex) pairs at distance > D from a_1 and from b_1. Zero means valid."""
    Sinv = [inv[s] for s in S]
    total = 0
    for root in (0, N):
        seen = [False] * (2 * N)
        seen[root] = True
        frontier = [root]
        reached = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for s in S:
                        v = N + row[s]
                        if not seen[v]:
                            seen[v] = True
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for si in Sinv:
                        v = row[si]
                        if not seen[v]:
                            seen[v] = True
                            nxt.append(v)
            reached += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - reached
    return total


def _anneal(N, T, inv, d, D, rng, t_end, iters):
    """Anneal a connection set S (containing the identity 0) to get cost 0. Returns S or None."""
    if d < 2 or d > N:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cost = _cost(N, T, inv, S, D)
    if cost == 0:
        return S
    temp = 2.0
    for _ in range(iters):
        if time.monotonic() >= t_end:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(N)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _cost(N, T, inv, S2, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cost = S2, c2
            if cost == 0:
                return S
        temp = max(0.05, temp * 0.998)
    return None


def _haar_search(d, D, deadline, rng, lo, hi):
    """Search group Haar graphs with order N in [lo, hi]; return the largest valid (n, edges) found."""
    best = None
    hi = min(hi, 400)
    while time.monotonic() < deadline and lo <= hi:
        N = rng.randint(lo, hi)
        cands = _groups_of_order(N)
        m, k, r = rng.choice(cands)
        _, T, inv = _table(m, k, r)
        slice_end = min(deadline, time.monotonic() + 1.5)
        S = _anneal(N, T, inv, d, D, rng, slice_end, 100000)
        if S is not None:
            edges = [(g, N + T[g][s]) for g in range(N) for s in S]
            best = (2 * N, edges)
            lo = N + 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
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

    pg_found = False
    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
            pg_found = True

    if d >= 2 and not (D == 3 and pg_found):
        moore_half = max(d, lib._moore_bound(d, D) // 2)
        lo = max(d, best_n // 2 + 1)
        hi = min(moore_half, 400)
        res = _haar_search(d, D, deadline, rng, lo, hi)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
