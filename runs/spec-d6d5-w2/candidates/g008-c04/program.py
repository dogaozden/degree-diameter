import math
import random
import time
from math import gcd

import lib


# ----------------------------------------------------------------------------
# Baseline families (cheap, always tried first): projective plane incidence
# graphs for D >= 3 and the Araujo-Pardo-Lopez graph for d = q + 2.
# ----------------------------------------------------------------------------

def _pg(d):
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
# Main new construction: bi-Cayley (Haar-type) graphs over non-abelian groups.
#
# Group G = Z_m x| Z_k (semidirect, all valid r). Vertices A_g and B_h, with
# A_g adjacent to B_{g*s} for each s in S, |S| = d. Left multiplication is an
# automorphism that is transitive on each side, so the graph has diameter <= D
# iff BFS from A_e and from B_e both reach everything within D steps.
# That makes each cost evaluation two BFS passes, not n of them.
#
# Non-abelian groups such as AGL(1, 19) = Z_19 x| Z_18 (order 342, so a
# 684-vertex graph) are sampled here, which the earlier search did not do.
# Order is searched by bisection, then pushed upward.
# ----------------------------------------------------------------------------

def _reach(adj, src, D, N):
    """Number of vertices within distance D of src."""
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
    return cnt


def _anneal_group(G, mul, inv, d, D, rng, deadline):
    """Anneal a connection set S (|S| = d) in the group. Returns S with zero cost, or None."""
    if G < d:
        return None
    invs = [inv(x) for x in range(G)]
    cache = {}

    def R(t):
        """R(t)[x] = mul(x, t), memoised."""
        r = cache.get(t)
        if r is None:
            r = [mul(x, t) for x in range(G)]
            cache[t] = r
        return r

    N = 2 * G

    def cost(S):
        Rs = [R(s) for s in S]
        Ri = [R(invs[s]) for s in S]
        adj = [[G + Rt[g] for Rt in Rs] for g in range(G)]
        adj += [[Rt[h] for Rt in Ri] for h in range(G)]
        return (N - _reach(adj, 0, D, N)) + (N - _reach(adj, G, D, N))

    S = rng.sample(range(G), d)
    c = cost(S)
    T = 1.0
    while c > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = cost(S2)
        T = max(0.05, T * 0.999)
        if c2 <= c - T * math.log(1.0 - rng.random()):
            S, c = S2, c2
    return S if c == 0 else None


def _edges_of(G, mul, S):
    """Edge list of the bi-Cayley graph over group elements 0..G-1 with connection set S."""
    E = []
    for s in S:
        Rs = [mul(g, s) for g in range(G)]
        for g in range(G):
            E.append((g, G + Rs[g]))
    return 2 * G, E


def _attempt(G, d, D, end, rng):
    """Try random semidirect groups of order G until `end`. Returns (n, edges) or None."""
    options = []
    for k in range(1, G + 1):
        if G % k == 0 and G // k >= 2:
            m = G // k
            rs = [r for r in range(1, m) if gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if rs:
                options.append((m, k, rs))
    if not options:
        return None
    while time.monotonic() < end:
        m, k, rs = rng.choice(options)
        r = rng.choice(rs)
        try:
            order, mul, inv = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        sub_end = min(end, time.monotonic() + 2.0)
        S = _anneal_group(order, mul, inv, d, D, rng, sub_end)
        if S is not None:
            return _edges_of(order, mul, S)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = list(lib.haar_graph(d, range(d)))

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    moore = lib.moore_bound(d, D)

    if D >= 3:
        pg = _pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 3 and d >= 2 and best[0] < moore:
        # Bisection on the group order G (n = 2G), then push just above the best.
        lo = best[0] // 2
        hi = min(420, moore // 2 + 1)
        probe = max(2.0, 0.12 * time_limit)
        while time.monotonic() < deadline - 0.5:
            if hi - lo > 2:
                G = (lo + hi) // 2
            else:
                G = lo + 1 + rng.randrange(3)
            end = min(deadline, time.monotonic() + probe)
            sol = _attempt(G, d, D, end, rng)
            if sol is not None:
                consider(sol[0], sol[1])
                lo = max(lo, G)
            elif G > lo:
                hi = min(hi, G)

    n, e = best[0], best[1]
    if not lib.is_valid(n, e, d, D):
        n, e = lib.haar_graph(d, range(d))
    return n, e
