"""Bold rewrite: bitset-accelerated multi-base cyclic lifts with annealed voltages.

Strategy for D >= 4 (the weak family): a lift of a d-regular bipartite base
multigraph on k + k vertices by Z_N. Dart (i, j, s) joins A_{i,x} to B_{j,x+s}.
Reachability is evaluated with Python big-int bitsets, where a Z_N shift is a
rotation of an N-bit integer. This makes each evaluation far cheaper than the
set-based BFS, so many more voltage configurations can be tested per second.
Each run anneals voltages (and layer permutations for k >= 2) to zero unreached
pairs, then the search moves to a slightly larger order.

Fallbacks: K_{d,d} (diameter 2) for D = 2, PG(2, d-1) incidence for D = 3 when
d-1 is a prime power, and K_{d,d} if any final check fails. Every returned graph
passes lib.is_valid.
"""
import math
import random
import time

import lib


ATTEMPT_ITERS = 4000   # annealing steps per (k, N) attempt


def _rot(X, s, N, mask):
    """Bitset of {x + s mod N : x in X} for an N-bit bitset X."""
    if s == 0:
        return X
    return ((X << s) | (X >> (N - s))) & mask


def _distinct(darts):
    """True if no two darts share (i, j, s), i.e. the lift has no multi-edges."""
    return len(set(darts)) == len(darts)


def _darts(P, V, d, k):
    return [(i, P[L][i], V[L][i]) for L in range(d) for i in range(k)]


def _cost(k, N, D, darts):
    """Number of (source, vertex) pairs at distance > D, summed over all 2k sources.

    Z_N translations act transitively on each side, so sources A_{i,0} and B_{j,0}
    suffice. Zero means the lift has diameter <= D.
    """
    mask = (1 << N) - 1
    full = 2 * k * N
    back = [(N - s) % N for (_, _, s) in darts]
    total = 0
    sources = [(0, i) for i in range(k)] + [(1, j) for j in range(k)]
    for side, src in sources:
        visA = [0] * k
        visB = [0] * k
        fA = [0] * k
        fB = [0] * k
        if side == 0:
            visA[src] = 1
            fA[src] = 1
        else:
            visB[src] = 1
            fB[src] = 1
        for _ in range(D):
            nA = [0] * k
            nB = [0] * k
            for idx, (i, j, s) in enumerate(darts):
                f = fA[i]
                if f:
                    nB[j] |= _rot(f, s, N, mask)
                g = fB[j]
                if g:
                    nA[i] |= _rot(g, back[idx], N, mask)
            any_new = False
            for j in range(k):
                x = nB[j] & ~visB[j]
                nB[j] = x
                if x:
                    visB[j] |= x
                    any_new = True
            for i in range(k):
                x = nA[i] & ~visA[i]
                nA[i] = x
                if x:
                    visA[i] |= x
                    any_new = True
            fA, fB = nA, nB
            if not any_new:
                break
        reached = sum(v.bit_count() for v in visA) + sum(v.bit_count() for v in visB)
        total += full - reached
    return total


def _anneal(d, D, k, N, rng, deadline, iters):
    """Anneal voltages and layer permutations until the lift has diameter <= D.

    Returns the dart list on success, else None.
    """
    P = None
    darts = None
    for _ in range(100):
        P = [rng.sample(range(k), k) for _ in range(d)]
        V = [[rng.randrange(N) for _ in range(k)] for _ in range(d)]
        darts = _darts(P, V, d, k)
        if _distinct(darts):
            break
    else:
        return None

    cost = _cost(k, N, D, darts)
    T0 = 1.0 + 0.02 * cost
    for step in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - step / iters) + 0.05
        if k == 1 or rng.random() < 0.75:
            L = rng.randrange(d)
            i = rng.randrange(k)
            old = V[L][i]
            new = rng.randrange(N)
            if new == old:
                continue
            V[L][i] = new
            cand = _darts(P, V, d, k)
            if not _distinct(cand):
                V[L][i] = old
                continue
            c2 = _cost(k, N, D, cand)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
                darts = cand
            else:
                V[L][i] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            P[L][a], P[L][b] = P[L][b], P[L][a]
            cand = _darts(P, V, d, k)
            if not _distinct(cand):
                P[L][a], P[L][b] = P[L][b], P[L][a]
                continue
            c2 = _cost(k, N, D, cand)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
                darts = cand
            else:
                P[L][a], P[L][b] = P[L][b], P[L][a]

    return darts if cost == 0 else None


def _lift_edges(k, N, darts):
    """Expand darts into the simple bipartite graph on 2kN vertices.

    A_{i,x} is vertex i*N + x and B_{j,y} is vertex (k + j)*N + y.
    """
    E = []
    for i, j, s in darts:
        for x in range(N):
            E.append((i * N + x, (k + j) * N + (x + s) % N))
    return 2 * k * N, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every d >= 1.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)
    rng = random.Random(seed)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Projective plane baseline for D = 3 (d = 3 gives the Fano incidence graph, 14 vertices).
    if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))

    try:
        while time.monotonic() < deadline and best[0] < moore:
            n_best = best[0]
            if n_best // 2 + 1 > moore // 2:
                break
            k = rng.choice((1, 2, 2, 3, 3, 4))
            lo = n_best // (2 * k) + 1          # need 2*k*N > n_best
            hi_cap = moore // (2 * k)
            if lo > hi_cap:
                continue
            window = max(2, lo // 25)
            N = lo + rng.randrange(window)
            if N > hi_cap:
                N = lo
            if N < d:
                continue
            darts = _anneal(d, D, k, N, rng, deadline, ATTEMPT_ITERS)
            if darts is not None:
                n2, e2 = _lift_edges(k, N, darts)
                consider(n2, e2)
    except Exception:
        pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
