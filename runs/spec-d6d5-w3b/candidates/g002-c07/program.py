import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Cheap baselines: projective plane incidence (D = 3) and Araujo-Pardo-Lopez.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family: Haar graphs over NON-ABELIAN groups.
#
# Group G of order N with connection set S (|S| = d, distinct elements).
# Left vertex g joins right vertex h iff h = g*s for some s in S.
# Every such graph is d-regular, bipartite, with 2N vertices, and simple.
# Left multiplication by G is an automorphism, so the diameter is decided by
# two BFS runs: one from left identity and one from right identity.
# Search: simulated annealing over S, cost = number of unreached vertices.
# ----------------------------------------------------------------------------

def _random_group(N, rng):
    """Random semidirect product Z_m x| Z_k of order N. Returns (order, rows, invs) or None.

    rows[x][y] is the product x*y in the group, coded as integers 0..N-1 (identity is 0).
    """
    cyc, noncyc = [], []
    for k in range(1, 13):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k == 1:
            cyc.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                noncyc.append((m, k, r))
    if not cyc and not noncyc:
        return None
    if noncyc and (not cyc or rng.random() < 0.7):
        m, k, r = rng.choice(noncyc)
    else:
        m, k, r = rng.choice(cyc)
    try:
        order, mul, inv = lib.semidirect_group(m, k, r)
    except ValueError:
        return None
    rows = [[mul(x, y) for y in range(order)] for x in range(order)]
    invs = [inv(x) for x in range(order)]
    return order, rows, invs


def _unreached(N, D, rows, S, invS, side, src):
    """Number of the 2N vertices NOT within distance D of the source (side 0 = left, 1 = right)."""
    seenL = bytearray(N)
    seenR = bytearray(N)
    if side == 0:
        seenL[src] = 1
        frontier = [(0, src)]
    else:
        seenR[src] = 1
        frontier = [(1, src)]
    cnt = 1
    for _ in range(D):
        if not frontier:
            break
        nxt = []
        for sd, x in frontier:
            row = rows[x]
            if sd == 0:
                for s in S:
                    y = row[s]
                    if not seenR[y]:
                        seenR[y] = 1
                        nxt.append((1, y))
            else:
                for s in invS:
                    y = row[s]
                    if not seenL[y]:
                        seenL[y] = 1
                        nxt.append((0, y))
        cnt += len(nxt)
        frontier = nxt
    return 2 * N - cnt


def _haar_cost(N, D, rows, inv, S):
    """Zero iff the Haar graph with connection set S has diameter <= D (by transitivity)."""
    invS = [inv[s] for s in S]
    return (_unreached(N, D, rows, S, invS, 0, 0)
            + _unreached(N, D, rows, S, invS, 1, 0))


def _anneal_haar(N, D, rows, inv, d, rng, deadline):
    """Anneal a connection set S of size d in G. Returns (S or None, cost)."""
    S = rng.sample(range(N), d)
    cost = _haar_cost(N, D, rows, inv, S)
    it = 0
    while cost > 0:
        it += 1
        if (it & 15) == 0 and time.monotonic() >= deadline:
            break
        T = max(0.3, 3.0 * (0.9995 ** it))
        i = rng.randrange(d)
        new = rng.randrange(N)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _haar_cost(N, D, rows, inv, S)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            S[i] = old
    return (S if cost == 0 else None), cost


def _haar_edges(N, rows, S):
    """Edge list of the Haar graph: left g joined to right N + rows[g][s] for s in S."""
    E = [(g, N + rows[g][s]) for g in range(N) for s in S]
    return 2 * N, E


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best_n, best_e = fb_n, fb_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 2:
        return fb_n, fb_e

    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
    ar = _araujo(d)
    if ar is not None:
        consider(ar[0], ar[1])

    # Main search: non-abelian Haar graphs of order N, so the graph has 2N vertices.
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline - 1.0 and best_n < moore:
        lo = max(d, best_n // 2 + 1)
        if 2 * lo > moore:
            break
        N = lo + rng.randrange(0, 6)
        if 2 * N > moore:
            N = lo
        g = _random_group(N, rng)
        if g is None:
            continue
        order, rows, invs = g
        cap = min(deadline, time.monotonic() + 5.0)
        S, _ = _anneal_haar(order, D, rows, invs, d, rng, cap)
        if S is not None:
            n, e = _haar_edges(order, rows, S)
            consider(n, e)

    if not lib.is_valid(best_n, best_e, d, D):
        return fb_n, fb_e
    return best_n, best_e
