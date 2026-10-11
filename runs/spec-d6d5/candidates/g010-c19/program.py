import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: projective plane incidence graph and Araujo-Pardo-Lopez graph.
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
# New family: bipartite doubles of Cayley digraphs Cay(G, S), |S| = d.
#
# Vertices A_g = g and B_h = N + h, with A_g adjacent to B_{g*s} for s in S.
# Left multiplication by a group element is an automorphism, so the diameter
# condition only has to be checked from the two sources A_identity and
# B_identity. The graph is d-regular, bipartite, and simple (S has distinct
# elements), so it is valid whenever both eccentricities are at most D.
# ----------------------------------------------------------------------------

def _groups(N, rng, cap=10):
    """Random sample of semidirect products Z_m x| Z_k of order N, as (order, mul, inv)."""
    opts = []
    for k in range(1, N + 1):
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
    rng.shuffle(opts)
    out = []
    for m, k, r in opts[:cap]:
        try:
            out.append(lib.semidirect_group(m, k, r))
        except ValueError:
            continue
    return out


def _tables(N, mul, inv):
    """Multiplication table and inverse table for a group of order N with elements 0..N-1."""
    tab = [[mul(g, h) for h in range(N)] for g in range(N)]
    invt = [inv(x) for x in range(N)]
    return tab, invt


def _adj(N, tab, invt, S):
    """Adjacency lists of the bipartite double of Cay(G, S)."""
    Sinv = [invt[s] for s in S]
    adj = [None] * (2 * N)
    for g in range(N):
        row = tab[g]
        adj[g] = [N + row[s] for s in S]
    for h in range(N):
        row = tab[h]
        adj[N + h] = [row[t] for t in Sinv]
    return adj


def _cost(N, adj, D):
    """Number of (source, vertex) pairs at distance more than D from the two sources. Zero means valid."""
    n = 2 * N
    total = 0
    for src in (0, N):
        seen = bytearray(n)
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
        total += n - cnt
    return total


def _anneal(N, tab, invt, d, D, rng, deadline, iters):
    """Simulated annealing over connection sets S of size d. Returns S with zero cost, or None."""
    S = rng.sample(range(N), d)
    c = _cost(N, _adj(N, tab, invt, S), D)
    for it in range(iters):
        if c == 0:
            return S
        if time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        T2 = S[:]
        T2[i] = x
        c2 = _cost(N, _adj(N, tab, invt, T2), D)
        T = max(0.3, 3.0 * (1.0 - it / iters))
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = T2, c2
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    state = {"best": best}

    def consider(n, e):
        if n > state["best"][0] and lib.is_valid(n, e, d, D):
            state["best"] = (n, e)

    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])
    ar = _araujo(d)
    if ar is not None:
        consider(ar[0], ar[1])

    moore = lib._moore_bound(d, D)
    if state["best"][0] >= moore:
        return state["best"]

    # Main search: bipartite Cayley doubles over sampled groups of order N,
    # so the graph has 2N vertices. Only orders above the current best are tried.
    while time.monotonic() < deadline:
        cur = state["best"][0]
        lo = max(2, cur // 2 + 1)
        if lo > moore // 2:
            break
        hi = min(moore // 2, lo + 24)
        N = rng.randint(lo, hi)
        gs = _groups(N, rng)
        if not gs:
            continue
        order, mul, inv = rng.choice(gs)
        tab, invt = _tables(order, mul, inv)
        S = _anneal(order, tab, invt, d, D, rng, deadline, 500)
        if S is not None:
            e = [(g, order + tab[g][s]) for g in range(order) for s in S]
            consider(2 * order, e)

    best = state["best"]
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
