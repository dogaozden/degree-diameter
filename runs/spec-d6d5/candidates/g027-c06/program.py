import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline: projective plane incidence graph PG(2, q) (diameter 3),
# with q the largest prime power satisfying q + 1 <= d.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New main family: bi-Cayley ("Cayley-bipartite") graphs over finite groups.
#
# For a group G and a connection set S (|S| = d, distinct elements), put
#   a_g = g          (left side, indices 0..G-1)
#   b_x = G + x      (right side, indices G..2G-1)
# and join a_g to b_{g*s} for every s in S. Left multiplication by h is an
# automorphism that acts transitively on each side, so the diameter is at most
# D iff every vertex is within distance D of a_e and of b_e. Two BFS runs
# therefore decide validity.
#
# Groups are semidirect products Z_m x| Z_k (lib.semidirect_group), including
# cyclic groups (k = 1) and direct products (r = 1).
# ----------------------------------------------------------------------------

def _group(G, rng):
    """Random group of order G from Z_m x| Z_k with k <= 12. Returns (order, mul, inv)."""
    divs = [k for k in range(1, min(12, G) + 1) if G % k == 0 and G // k >= 2]
    k = rng.choice(divs)
    m = G // k
    if k == 1:
        r = 1
    else:
        # r = 1 is always a candidate, so this list is never empty.
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        r = rng.choice(cands)
    return lib.semidirect_group(m, k, r)


def _tabs(cache, mul, inv, G, s):
    """Cached right-multiplication tables for s: (g -> g*s, x -> x*s^{-1})."""
    t = cache.get(s)
    if t is None:
        si = inv(s)
        t = ([mul(g, s) for g in range(G)], [mul(g, si) for g in range(G)])
        cache[s] = t
    return t


def _cost(G, D, tabs):
    """Number of (source, vertex) pairs not reached within D from a_e and from b_e."""
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for ra, _rb in tabs:
                        v = G + ra[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    x = u - G
                    for _ra, rb in tabs:
                        v = rb[x]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _search(d, D, G, mul, inv, rng, deadline, iters):
    """Simulated annealing over S (|S| = d) for a valid bi-Cayley graph of order 2G."""
    cache = {}
    S = rng.sample(range(G), d)

    def cur(S_):
        return [_tabs(cache, mul, inv, G, s) for s in S_]

    c = _cost(G, D, cur(S))
    T = 3.0
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        T = max(0.3, T * 0.998)
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _cost(G, D, cur(S))
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            S[i] = old
    return (list(S) if c == 0 else None), c


def _edges(G, S, mul):
    """Edge list of the bi-Cayley graph with connection set S over a group of order G."""
    E = []
    for g in range(G):
        for s in S:
            E.append((g, G + mul(g, s)))
    return 2 * G, E


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

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best_n and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
            best_n = pg[0]

    moore = lib._moore_bound(d, D)
    try:
        while time.monotonic() < deadline and best_n < moore:
            lo = max(best_n // 2 + 1, d + 1, 2)
            G = rng.randint(lo, lo + max(2, lo // 25))
            order, mul, inv = _group(G, rng)
            sub = min(deadline, time.monotonic() + max(1.5, min(8.0, 0.2 * time_limit)))
            while time.monotonic() < sub:
                S, _c = _search(d, D, order, mul, inv, rng, sub, 4000)
                if S is not None:
                    n, e = _edges(order, S, mul)
                    if n > best_n and lib.is_valid(n, e, d, D):
                        best = (n, e)
                        best_n = n
                    break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
