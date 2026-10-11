import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction families.
#
# Main family (new): Haar graphs H(G, S) over finite groups G of order N with
# |S| = d. Vertices are (g, 0) and (g, 1) for g in G, and (g, 0) ~ (s*g, 1)
# for s in S. Right multiplication is an automorphism, so distances from the
# two identity vertices determine the diameter. Groups are semidirect products
# Z_m x| Z_k of order N, which include non-abelian groups.
#
# Safe fallbacks: K_{d,d}, and the projective-plane incidence graph when
# d-1 is a prime power (valid for D >= 3).
# ----------------------------------------------------------------------------


def _pg_graph(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _groups(N):
    """All semidirect products Z_m x| Z_k of order N with m >= 2, as (m, k, r) triples."""
    out = []
    for k in range(1, N + 1):
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
    """Multiplication table T[x][y] = x*y, and inverse list I, for the group Z_m x| Z_k."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, y) for y in range(order)] for x in range(order)]
    I = [inv(x) for x in range(order)]
    return order, T, I


def _nb(N, T, I, S):
    """Neighbour lists for the Haar graph of S. Side 0 is 0..N-1, side 1 is N..2N-1."""
    nb0 = [[N + T[s][g] for s in S] for g in range(N)]
    nb1 = [[T[I[s]][y] for s in S] for y in range(N)]
    return nb0, nb1


def _cost(N, nb0, nb1, D):
    """Number of vertex pairs (source, vertex) not within distance D, for the two identity sources.

    Zero iff the Haar graph has diameter at most D.
    """
    tot = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                nbrs = nb0[u] if u < N else nb1[u - N]
                for v in nbrs:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        tot += 2 * N - cnt
    return tot


def _anneal(N, d, D, T, I, rng, deadline, iters):
    """Simulated annealing over connection sets S of size d containing the identity."""
    if d < 2 or N - 1 < d - 1:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    nb0, nb1 = _nb(N, T, I, S)
    cost = _cost(N, nb0, nb1, D)
    t0, t1 = 2.0, 0.05
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = t0 * (t1 / t0) ** (it / iters)
        i = rng.randrange(1, d)
        x = rng.randrange(1, N)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        n0, n1 = _nb(N, T, I, S)
        c2 = _cost(N, n0, n1, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = c2
            nb0, nb1 = n0, n1
        else:
            S[i] = old
    return S if cost == 0 else None


def _haar_edges(N, T, S):
    """Edges of the Haar graph: (g, 0) ~ (s*g, 1) for s in S."""
    return [(g, N + T[s][g]) for g in range(N) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2 or d < 2:
        return best

    # Projective plane incidence graph (diameter 3).
    if D >= 3:
        pg = _pg_graph(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: Haar graphs over non-abelian and cyclic groups of order N.
    # The target order is 2N, so we look for N just above best_n // 2.
    misses = 0
    iters = 1500
    while time.monotonic() < deadline:
        N = max(best_n // 2 + 1 + misses, d + 1)
        groups = _groups(N)
        if not groups:
            misses += 1
            continue
        rng.shuffle(groups)
        found = False
        for (m, k, r) in groups[:4]:
            if time.monotonic() > deadline:
                break
            order, T, I = _table(m, k, r)
            S = _anneal(order, d, D, T, I, rng, deadline, iters)
            if S is not None:
                consider(2 * order, _haar_edges(order, T, S))
                found = True
                break
        misses = 0 if found else misses + 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
