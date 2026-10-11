import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families (cheap, always tried first).
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
# Bold secondary construction: bi-Cayley graphs over non-abelian groups.
#
# Groups G = Z_m x| Z_k (lib.semidirect_group). Vertices A_g = g and B_h = N + h.
# Edge A_g -- B_{g*s} for each s in S, |S| = d (S distinct, so the graph is simple
# and d-regular on both sides).
#
# Left multiplication by any h is an automorphism (A_g -> A_{hg}, B_x -> B_{hx}),
# so each side is vertex-transitive. Hence the graph has diameter <= D iff
# the BFS from A_e and from B_e both reach all 2N vertices within D steps.
# Two BFS runs per cost evaluation instead of 2N.
# ----------------------------------------------------------------------------

def _bfs_bad(N, D, perms, invp, src):
    """Number of vertices NOT within distance D of src in the bi-Cayley graph."""
    seen = bytearray(2 * N)
    seen[src] = 1
    frontier = [src]
    count = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < N:
                for p in perms:
                    v = N + p[u]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                h = u - N
                for p in invp:
                    v = p[h]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        if not nxt:
            break
        count += len(nxt)
        frontier = nxt
    return 2 * N - count


def _group_candidates(N, max_k):
    """All (m, k, r) with m * k = N, m >= 2, k <= max_k, valid semidirect data."""
    opts = []
    for k in range(1, min(N, max_k) + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _search_group(N, D, d, mul, inv, rng, deadline, steps):
    """Anneal the connection set S (|S| = d) in the group of order N. Returns (S or None, cost)."""
    cache = {}

    def R(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(N)]
            cache[s] = p
        return p

    def cost(S):
        perms = [R(s) for s in S]
        invp = [R(inv(s)) for s in S]
        return _bfs_bad(N, D, perms, invp, 0) + _bfs_bad(N, D, perms, invp, N)

    S = rng.sample(range(N), d)
    c = cost(S)
    T = 1.0
    for _ in range(steps):
        if c == 0 or time.monotonic() > deadline:
            break
        t = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        T2 = list(S)
        T2[t] = x
        c2 = cost(T2)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = T2, c2
        T = max(0.3, T * 0.995)
    return (S if c == 0 else None), c


def _lift(N, S, mul):
    """Edges of the bi-Cayley graph: A_g -- B_{g s}."""
    edges = set()
    for s in S:
        for g in range(N):
            edges.add((g, N + mul(g, s)))
    return 2 * N, sorted(edges)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
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

    moore = lib.moore_bound(d, D)
    if D == 2 or best_n >= moore:
        return best

    # Baselines.
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
    ar = _araujo(d)
    if ar is not None:
        consider(ar[0], ar[1])

    # Main bold search: bi-Cayley lifts over semidirect products, aiming to beat the record.
    lo_fail = 0
    while time.monotonic() < deadline and best_n < moore:
        lo = max(best_n // 2 + 1, d)
        hi_cap = moore // 2
        if lo > hi_cap:
            break
        span = min(hi_cap - lo, max(2, lo // 30) + lo_fail // 5)
        N = lo + rng.randint(0, span)

        opts = _group_candidates(N, 24)
        if not opts:
            lo_fail += 1
            continue
        rng.shuffle(opts)

        found = False
        for (m, k, r) in opts[:2]:
            if time.monotonic() >= deadline:
                break
            try:
                order, mul, inv = lib.semidirect_group(m, k, r)
            except ValueError:
                continue
            per_group_deadline = min(deadline, time.monotonic() + 6.0)
            S, _c = _search_group(order, D, d, mul, inv, rng, per_group_deadline, 600)
            if S is not None:
                n, e = _lift(order, S, mul)
                if consider(n, e):
                    found = True
                    break

        if found:
            lo_fail = 0
        else:
            lo_fail += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
