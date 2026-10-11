import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Constants.
# ----------------------------------------------------------------------------

MAX_GROUPS = 8        # groups of a given order N tried before moving on
BAND = 12             # sweep window above the lower bound before wrapping
CYC_ITERS = 20000     # annealing steps per restart for cyclic lifts (cheap)
GEN_ITERS = 800       # annealing steps per restart for non-abelian lifts
RESTARTS = 6          # independent annealing restarts per (N, group)
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# PG(2, q) baseline (exact for d-1 a prime power, D = 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Groups and cached multiplication tables for Z_m x|_r Z_k.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k, with T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


# ----------------------------------------------------------------------------
# NEW HELPER: bitset eccentricity cost for cyclic bi-Cayley graphs.
#
# For the cyclic bi-Cayley graph A_x ~ B_{x+g} (g in S, Z_N), the sets of A- and
# B-vertices within distance t of a source are N-bit integers. One expansion step
# is a union of cyclic rotations, so the whole ball of radius D from A_0 and B_0
# is computed in O(D * d) big-int operations instead of a Python BFS.
# Left translation is an automorphism that is transitive on each side, so the
# two sources A_0, B_0 determine all distances. Returns the number of
# (source, vertex) pairs not reached within D (zero means diameter <= D).
# ----------------------------------------------------------------------------

def _unreached_cyclic(N, S, D):
    mask = (1 << N) - 1
    shifts = sorted({g % N for g in S})
    negs = [(-g) % N for g in shifts]

    def rot(x, g):
        """Rotate the N-bit set x by g: bit a moves to bit (a + g) mod N."""
        if g == 0:
            return x
        return ((x << g) | (x >> (N - g))) & mask

    total = 0
    for src in (0, 1):
        RA = 1 if src == 0 else 0
        RB = 1 if src == 1 else 0
        for _ in range(D):
            fa = 0                      # B-neighbours of the A-ball
            for g in shifts:
                fa |= rot(RA, g)
            fb = 0                      # A-neighbours of the B-ball
            for g in negs:
                fb |= rot(RB, g)
            nRA = RA | fb
            nRB = RB | fa
            if nRA == RA and nRB == RB:
                break
            RA, RB = nRA, nRB
        total += 2 * N - RA.bit_count() - RB.bit_count()
    return total


def _unreached_table(N, T, invs, S, D):
    """Generic (non-abelian) version of the cost, using BFS over the group table."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


# ----------------------------------------------------------------------------
# Simulated annealing over connection sets S (with 0 fixed WLOG, since right
# multiplication of S is an isomorphism of the bi-Cayley graph).
# ----------------------------------------------------------------------------

def _anneal(N, cost, d, rng, deadline, iters):
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = cost(S)
    T0, T_end = 1.0, 0.05
    for it in range(iters):
        if cur == 0:
            break
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        temp = T0 + (T_end - T0) * (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = cost(S)
        if v <= cur or rng.random() < math.exp((cur - v) / temp):
            cur = v
        else:
            S[i] = old
    return S if cur == 0 else None


def _search_order(N, d, D, rng, deadline):
    """Try to find a valid bi-Cayley lift on a group of order N; return (S, T) or None.

    T is None for the cyclic group (edges are then x ~ N + (x+g) mod N).
    """
    if N < d:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k2, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        if k2 == 1:
            cost = lambda S, N=N: _unreached_cyclic(N, S, D)
            T = None
            iters = CYC_ITERS
        else:
            _, _, T, invs = _tables(m, k2, r)
            cost = lambda S, N=N, T=T, invs=invs: _unreached_table(N, T, invs, S, D)
            iters = GEN_ITERS
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                return None
            S = _anneal(N, cost, d, rng, deadline, iters)
            if S is not None:
                return S, T
    return None


def _bicayley_edges(N, S, T):
    if T is None:
        return [(x, N + (x + g) % N) for x in range(N) for g in S]
    return [(x, N + T[x][g]) for x in range(N) for g in S]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is the fallback.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: bi-Cayley lifts with 2N vertices, sweeping N upward from the
    # smallest order that would beat the current best.
    sweep = None
    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > moore // 2:
            break
        if sweep is None or sweep < lo or sweep > lo + BAND:
            sweep = lo
        N = sweep
        sweep += 1
        res = _search_order(N, d, D, rng, deadline)
        if res is not None:
            S, T = res
            consider(2 * N, _bicayley_edges(N, S, T))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
