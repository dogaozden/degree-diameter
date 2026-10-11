import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: cyclic bi-Cayley graphs found by simulated annealing.
#
# Vertices: a_g (g in Z_N) and b_h (h in Z_N); a_g ~ b_{g+s} for s in S, |S| = d.
# Every vertex has degree d and the graph is bipartite. Translations and the
# swap a_g <-> b_{-g} are automorphisms, so the diameter equals the eccentricity
# of a_0. The search anneals S to minimise the number of vertices farther than D
# from a_0, using bitmask BFS on the cyclic group.
#
# Order is 2N. The search bisects over N, and every candidate is verified with
# lib.is_valid. K_{d,d} (or the projective plane for D = 3) is the safe fallback.
# ----------------------------------------------------------------------------


def _rot(x, s, N, full):
    """Bitmask of {g + s : g in x} in Z_N."""
    if s == 0:
        return x
    return ((x << s) | (x >> (N - s))) & full


def _cost(N, S, D, full):
    """Number of vertices at distance > D from a_0 (both sides)."""
    reach_a = 1
    reach_b = 0
    frontier = 1
    side_a = True
    for _ in range(D):
        new = 0
        if side_a:
            for s in S:
                new |= _rot(frontier, s, N, full)
            new &= full ^ reach_b
            reach_b |= new
        else:
            for s in S:
                new |= _rot(frontier, (N - s) % N, N, full)
            new &= full ^ reach_a
            reach_a |= new
        frontier = new
        side_a = not side_a
        if not frontier:
            break
    return (N - reach_a.bit_count()) + (N - reach_b.bit_count())


def _search(N, d, D, deadline, rng):
    """Anneal a d-element connection set S in Z_N with zero cost; return S or None."""
    full = (1 << N) - 1
    iters = 30000
    T0, T1 = 2.0, 0.1
    decay = (T1 / T0) ** (1.0 / iters)
    while time.monotonic() < deadline:
        S = rng.sample(range(N), d)
        c = _cost(N, S, D, full)
        T = T0
        for it in range(iters):
            if c == 0:
                return S
            if (it & 1023) == 0 and time.monotonic() >= deadline:
                return None
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in S:
                continue
            old = S[i]
            S[i] = x
            c2 = _cost(N, S, D, full)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                c = c2
            else:
                S[i] = old
            T *= decay
        if c == 0:
            return S
    return None


def _bicayley_edges(N, S):
    edges = []
    for g in range(N):
        for s in S:
            edges.append((g, N + (g + s) % N))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    moore = lib._moore_bound(d, D)

    # Projective plane incidence graph meets the Moore bound when d-1 is a prime power (D = 3).
    if D == 3 and lib.is_prime_power(d - 1):
        n2, e2 = lib.projective_plane_incidence(d - 1)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)

    if best[0] >= moore:
        return best

    rng = random.Random(seed)
    total = 0.8 * time_limit
    lo = d                                   # N = d is feasible (complete bipartite)
    hi = min(max(d, moore // 2), 1500)

    while lo < hi:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        budget = min(remaining, max(2.0, 0.2 * total))
        mid = (lo + hi + 1) // 2
        S = _search(mid, d, D, time.monotonic() + budget, rng)
        if S is not None:
            n2 = 2 * mid
            e2 = _bicayley_edges(mid, S)
            if lib.is_valid(n2, e2, d, D):
                if n2 > best[0]:
                    best = (n2, e2)
                lo = mid
                continue
        hi = mid - 1

    return best
