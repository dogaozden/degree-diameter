import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fallback bases: K_{d,d} (diameter 2) and the projective plane incidence graph.
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Single-layer bi-Cayley graphs over metacyclic groups Z_m x| Z_k.
#
# Vertices A_g = g and B_h = G + h for g, h in the group of order G.
# Connection set S (|S| = d, with the identity 0 in S WLOG) gives edges
# A_g -- B_{g s} for s in S. Left multiplication by a group element is an
# automorphism of the graph, so the diameter is at most D iff every vertex is
# within distance D of A_e and of B_e. The search hill-climbs S to minimise
# the number of unreached (source, vertex) pairs.
# ----------------------------------------------------------------------------

def _groups_of_order(G):
    """All (m, k, r) with m * k = G, m >= 2, defining Z_m x| Z_k with r^k = 1 mod m."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) != 1:
                continue
            if pow(r, k, m) != 1 % m:
                continue
            out.append((m, k, r))
    return out


def _unreached(G, mt, inv, S, D):
    """Number of (source, vertex) pairs not within distance D; sources are A_e and B_e."""
    N = 2 * G
    adj = [None] * N
    for g in range(G):
        row = mt[g]
        adj[g] = [G + row[s] for s in S]
    inv_S = [inv[s] for s in S]
    for h in range(G):
        row = mt[h]
        adj[G + h] = [row[t] for t in inv_S]
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
    return total


def _climb(G, mt, inv, d, D, rng, steps):
    """Hill-climb a connection set S of size d (containing 0); return S if it has diameter <= D."""
    S = [0] + rng.sample(range(1, G), d - 1)
    c = _unreached(G, mt, inv, S, D)
    for _ in range(steps):
        if c == 0:
            break
        i = rng.randrange(1, d)
        cand = rng.randrange(1, G)
        if cand in S:
            continue
        T = S[:]
        T[i] = cand
        ct = _unreached(G, mt, inv, T, D)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _try_order(G, d, D, rng, t_end):
    """Search groups of order G until t_end; return (n, edges) of a valid bi-Cayley graph or None."""
    groups = _groups_of_order(G)
    if not groups or G - 1 < d - 1:
        return None
    rng.shuffle(groups)
    it = 0
    while time_left(t_end):
        m, k, r = groups[it % len(groups)]
        it += 1
        _, mul, inv_f = lib.semidirect_group(m, k, r)
        mt = [[mul(x, y) for y in range(G)] for x in range(G)]
        inv = [inv_f(x) for x in range(G)]
        S = _climb(G, mt, inv, d, D, rng, 80)
        if S is not None:
            E = [(g, G + mt[g][s]) for g in range(G) for s in S]
            return 2 * G, E
    return None


def time_left(t_end):
    return time.monotonic() < t_end


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.0, min(0.8 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2:
        return best_n, best_e

    # Bipartite Moore bound caps the order; a bi-Cayley graph on 2G vertices needs G <= moore // 2.
    moore = lib.moore_bound(d, D)
    Gmax = moore // 2

    budget = 0.25
    while time_left(deadline):
        lo = best_n // 2 + 1
        if lo > Gmax:
            break
        progressed = False
        for G in range(lo, Gmax + 1):
            if not time_left(deadline):
                break
            t_end = min(deadline, time.monotonic() + budget)
            res = _try_order(G, d, D, rng, t_end)
            if res is not None:
                consider(res[0], res[1])
                progressed = True
                break
        if not progressed:
            budget *= 2

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, list(best_e)
