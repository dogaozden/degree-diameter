import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New helper: bitset cover cost for cyclic bi-Cayley graphs.
#
# The bi-Cayley graph over Z_N with connection set S (0 in S, |S| = d) has
# A_x ~ B_{x+s} for s in S. Translation by g is a cyclic rotation of an N-bit
# integer, so a whole BFS level is a few shifts and ORs on Python big ints.
# This makes each cost evaluation roughly an order of magnitude cheaper than
# list-based BFS, which allows far more annealing steps per second.
# ----------------------------------------------------------------------------

ANNEAL_ITERS = 4000


def _rot(x, g, N, full):
    """Bitmask of {(i + g) mod N : bit i of x set}."""
    if g == 0:
        return x
    return ((x << g) | (x >> (N - g))) & full


def _cover_cost(N, S, D, full):
    """Number of (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    negS = [(-s) % N for s in S]
    total = 0
    for src_side in (0, 1):
        if src_side == 0:
            va, vb, front, side = 1, 0, 1, 0
        else:
            va, vb, front, side = 0, 1, 1, 1
        for _ in range(D):
            if front == 0:
                break
            new = 0
            if side == 0:
                for s in S:
                    new |= _rot(front, s, N, full)
                new &= ~vb & full
                vb |= new
            else:
                for t in negS:
                    new |= _rot(front, t, N, full)
                new &= ~va & full
                va |= new
            front = new
            side ^= 1
        total += 2 * N - va.bit_count() - vb.bit_count()
    return total


def _anneal(N, d, D, rng, iters, deadline):
    """Simulated annealing over connection sets; returns S with zero cost, or None."""
    full = (1 << N) - 1
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cover_cost(N, S, D, full)
    T0 = 2.0
    for step in range(iters):
        if cur == 0:
            break
        if (step & 255) == 0 and time.monotonic() > deadline:
            return None
        T = T0 * (1.0 - step / iters) + 0.05
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _cover_cost(N, S, D, full)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = v
        else:
            S[i] = old
    return list(S) if cur == 0 else None


def _bicayley_edges(N, S):
    """Edges of the bi-Cayley graph over Z_N: A_x ~ B_{x+s}, with B_y numbered N + y."""
    return [(x, N + (x + s) % N) for x in range(N) for s in S]


# ----------------------------------------------------------------------------
# D = 3 structured baseline: incidence graph of PG(2, q).
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is the safe fallback.
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

    # Main search: cyclic bi-Cayley lifts on N base elements (2N vertices),
    # sampled just above the current best order.
    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > moore // 2:
            break
        lo = max(lo, d + 1)
        span = max(1, lo // 60)
        N = lo + rng.randrange(span)
        S = _anneal(N, d, D, rng, ANNEAL_ITERS, deadline)
        if S is not None:
            consider(2 * N, _bicayley_edges(N, S))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
