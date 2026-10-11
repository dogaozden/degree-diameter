import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe fallbacks: projective plane incidence (D >= 3) and Araujo-Pardo-Lopez
# (D >= 3, d = q + 2). Both are checked with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (q <= 31)."""
    for q in range(min(d - 1, 31), 1, -1):
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
# Bi-Cayley graphs over finite groups (the new, substantially different family).
#
# Group G = Z_m x| Z_k with r^k = 1 mod m (order N = m*k); elements coded as a*k+b,
# identity = 0. For a set S of d distinct group elements, the graph has
#   A-vertices g in G (ids 0..N-1),  B-vertices y in G (ids N..2N-1),
#   and edges A_g -- B_{g*s} for s in S.
# It is simple, d-regular and bipartite. Left multiplication by G is an
# automorphism, so the diameter is at most D iff every vertex is within D of
# A_e and of B_e. Two BFS runs therefore decide validity.
# ----------------------------------------------------------------------------

def _group_params(N):
    """All (m, k, r) with m*k = N giving Z_m x| Z_k, cyclic group included."""
    out = [(N, 1, 1)]
    for k in range(2, N // 2 + 1):
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
    """Multiplication table mt[x][y] = x*y and inverse list invl for Z_m x| Z_k."""
    N = m * k
    pw = [pow(r, b, m) for b in range(k)]
    yd = [divmod(y, k) for y in range(N)]
    mt = []
    for x in range(N):
        a, b = divmod(x, k)
        pb = pw[b]
        mt.append([((a + pb * c) % m) * k + (b + dd) % k for c, dd in yd])
    invl = [row.index(0) for row in mt]  # x * y = identity  <=>  y = x^{-1}
    return mt, invl


def _cost(N, mt, invl, S, D):
    """Number of (source, vertex) pairs not within D, for sources A_e and B_e. Zero iff valid."""
    invS = [invl[s] for s in S]
    total = 0
    for side in (0, 1):
        seen = bytearray(2 * N)
        src = side * N
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    row = mt[v]
                    for s in S:
                        w = N + row[s]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    row = mt[v - N]
                    for si in invS:
                        w = row[si]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _search(N, mt, invl, d, D, rng, deadline, iters):
    """Hill-climb a d-subset S of G, one element swapped at a time, until the cost is zero."""
    S = rng.sample(range(N), d)
    c = _cost(N, mt, invl, S, D)
    for _ in range(iters):
        if c == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        ct = _cost(N, mt, invl, T, D)
        if ct <= c or rng.random() < 0.02:
            S, c = T, ct
    return (S if c == 0 else None), c


def _edges(N, mt, S):
    """Edge list of the bi-Cayley graph: A_g = g, B_y = N + y, A_g ~ B_{g*s}."""
    return 2 * N, [(g, N + mt[g][s]) for g in range(N) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.78 * time_limit, time_limit - 6.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    rng = random.Random(seed)
    best = fallback
    best_n = fallback[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Algebraic starting points (valid for D >= 3).
    pg = _pg_candidate(d)
    if pg is not None:
        consider(pg[0], pg[1])
    ar = _araujo(d)
    if ar is not None:
        consider(ar[0], ar[1])

    # Main search: bi-Cayley graphs over groups of order N just above best_n / 2.
    while time.monotonic() < deadline:
        lo = max(d + 1, best_n // 2 + 1)
        N = lo + rng.choice((0, 0, 0, 0, 1, 1, 2, 4))
        cands = _group_params(N)
        if not cands:
            continue
        m, k, r = rng.choice(cands)
        mt, invl = _table(m, k, r)
        S, _ = _search(N, mt, invl, d, D, rng, deadline, 300)
        if S is not None:
            n, e = _edges(N, mt, S)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
