import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: projective plane incidence graph and Araujo-Pardo-Lopez graph.
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, d-1) when d-1 is a prime power (degree d, diameter 3)."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
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
# New family: Haar graphs (bi-Cayley graphs with one vertex class per side)
# over a catalogue of finite groups Z_m x| Z_k (including affine groups
# AGL(1,p) = Z_p x| Z_{p-1}, dihedral groups, and abelian groups).
#
# Graph on A_g, B_h (g, h in G): A_g ~ B_{g s} for s in S, |S| = d.
# Left multiplication by G acts transitively on A and on B, so the graph has
# diameter <= D iff BFS from A_e and from B_e both reach everything within D.
# ----------------------------------------------------------------------------

def _semidirect_options(G):
    """All (m, k, r) with m*k = G giving a valid semidirect product Z_m x| Z_k."""
    opts = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _tables(m, k, r):
    """Multiplication and inverse tables for the semidirect product (identity is code 0)."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(g, s) for s in range(order)] for g in range(order)]
    I = [inv(s) for s in range(order)]
    return T, I


def _cost(G, T, I, S, D, limit):
    """Number of vertices not reached within D from A_e and B_e (zero iff diameter <= D).

    Returns early with a value above `limit` once the running total exceeds it.
    """
    N = 2 * G
    adj = [[G + row[s] for s in S] for row in T]
    adj += [[T[h][I[s]] for s in S] for h in range(G)]
    total = 0
    for src in (0, G):
        seen = bytearray(N)
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
        total += N - cnt
        if total > limit:
            return total
    return total


def _search_S(G, T, I, d, D, rng, deadline, steps):
    """Annealed search for d distinct connection elements giving diameter <= D. None on failure."""
    S = rng.sample(range(G), d)
    c = _cost(G, T, I, S, D, float("inf"))
    for step in range(steps):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        temp = max(0.05, 1.5 * (1.0 - step / steps))
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        limit = c - temp * math.log(1.0 - rng.random())
        c2 = _cost(G, T, I, S2, D, limit)
        if c2 <= limit:
            S, c = S2, c2
    return S if c == 0 else None


def _sweep(d, D, lo, span, budget, deadline, rng, consider):
    """Try group orders G in [lo, lo+span), each with a time budget; report every success."""
    for G in range(lo, lo + span):
        if time.monotonic() >= deadline:
            return
        opts = _semidirect_options(G)
        if not opts:
            continue
        rng.shuffle(opts)
        gend = min(deadline, time.monotonic() + budget)
        for m, k, r in opts[:12]:
            if time.monotonic() >= gend:
                break
            T, I = _tables(m, k, r)
            S = _search_S(G, T, I, d, D, rng, gend, 600)
            if S is not None:
                edges = [(g, G + T[g][s]) for g in range(G) for s in S]
                consider(2 * G, edges)
                break


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Main search: Haar graphs over semidirect products, sweeping upward in order.
    while time.monotonic() < deadline:
        lo = max(d + 1, best_n // 2 + 1)
        _sweep(d, D, lo, 60, 2.0, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
