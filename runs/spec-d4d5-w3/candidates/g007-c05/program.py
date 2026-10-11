import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy: bi-Cayley graphs over small non-abelian groups.
#
# Vertices are G x {0,1}. Each connection element s in S (|S| = d, distinct)
# joins (g,0) to (g*s,1). Left multiplication is an automorphism, so the graph
# has diameter <= D iff every vertex is within D of (e,0) and of (e,1). The
# search therefore evaluates just two BFS runs per candidate. Groups are
# Z_m x| Z_k (via lib.semidirect_group), which gives more varied expansion than
# cyclic groups alone. The group order grows as valid graphs are found.
# ----------------------------------------------------------------------------

FRAC = 0.8          # fraction of time_limit used for searching
ATT_FRAC = 0.06    # per-group-attempt budget as a fraction of time_limit


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(G, rng):
    """Return (mul, inv) for a random semidirect product Z_m x| Z_k of order G."""
    opts = []
    for k2 in range(1, 13):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            rs = [1]
        else:
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if rs:
            opts.append((m, k2, rs))
    if not opts:
        return None
    m, k2, rs = rng.choice(opts)
    r = rng.choice(rs)
    _order, mul, inv = lib.semidirect_group(m, k2, r)
    return mul, inv


def _tables(G, mul, inv):
    """P[s][g] = g*s and invs[s] = s^{-1}, for all group elements."""
    P = [[mul(g, s) for g in range(G)] for s in range(G)]
    invs = [inv(s) for s in range(G)]
    return P, invs


def _reach(src, adj, D, N):
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


def _cost(G, S, P, invs, D):
    """Count of (representative, vertex) pairs at distance > D. Zero means valid."""
    N = 2 * G
    adj = [None] * N
    for g in range(G):
        adj[g] = [G + P[s][g] for s in S]
    for h in range(G):
        adj[G + h] = [P[invs[s]][h] for s in S]
    return sum(N - _reach(src, adj, D, N) for src in (0, G))


def _search(G, d, D, P, invs, rng, deadline):
    """Simulated-annealing-style search for S (|S| = d, distinct) with zero cost."""
    S = rng.sample(range(G), d)
    c = _cost(G, S, P, invs, D)
    best_c = c
    stall = 0
    T = 0.6
    while c > 0:
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T2 = S[:]
        T2[i] = x
        c2 = _cost(G, T2, P, invs, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = T2, c2
        if c < best_c:
            best_c = c
            stall = 0
        else:
            stall += 1
        if stall > 1500:
            S = rng.sample(range(G), d)
            c = _cost(G, S, P, invs, D)
            best_c = c
            stall = 0
    return S


def _bicayley_search(d, D, best, moore, deadline, time_limit, rng):
    """Grow the bi-Cayley order: search random groups near the current best and keep valid wins."""
    att = max(0.5, ATT_FRAC * time_limit)
    lo = best[0] // 2 + 1
    while time.monotonic() < deadline and best[0] < moore:
        if lo > moore // 2:
            break
        G = lo + rng.randrange(0, 3)
        G = min(max(G, d), moore // 2)
        g = _sample_group(G, rng)
        if g is None:
            continue
        mul, inv = g
        P, invs = _tables(G, mul, inv)
        att_end = min(deadline, time.monotonic() + att)
        S = _search(G, d, D, P, invs, rng, att_end)
        if S is None:
            continue
        n = 2 * G
        edges = [(x, G + P[s][x]) for s in S for x in range(G)]
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            lo = best[0] // 2 + 1
    return best


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + FRAC * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # K_{d,d} has diameter 2 and is the always-valid fallback.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback
    moore = lib._moore_bound(d, D)

    # Algebraic base for D >= 3 (projective plane incidence, diameter 3).
    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
                best = pg
                if best[0] >= moore:
                    return best
    except Exception:
        pass

    # Main search: bi-Cayley graphs over semidirect products.
    try:
        best = _bicayley_search(d, D, best, moore, deadline, time_limit, rng)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
