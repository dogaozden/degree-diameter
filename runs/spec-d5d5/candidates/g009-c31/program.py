import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# D = 3: projective plane incidence graph when d - 1 is a prime power.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New helper: bit-parallel bi-circulant search.
#
# A bi-circulant (bi-Cayley over Z_N) graph has parts A_x, B_x (x in Z_N) and
# edges A_x -- B_{x+s} for s in S, |S| = d. Vertex-transitivity under
# translation means only the eccentricities of A_0 and B_0 need checking.
#
# Instead of list-based BFS, each BFS level is a Python big-int bitmask over
# Z_N, and "shift every element by s" is a cyclic rotation done with two
# shifts and a mask. This makes the cost of a candidate S roughly an order of
# magnitude cheaper than list BFS, so annealing can run many more steps.
# ----------------------------------------------------------------------------

def _rot(X, s, N, full):
    """Cyclic rotation of the N-bit set X: element x maps to (x + s) mod N."""
    if s == 0:
        return X
    return ((X << s) | (X >> (N - s))) & full


def _unreached(N, Sp, Sn, D, full):
    """Number of (source, vertex) pairs at distance > D, sources A_0 and B_0.

    Sp are the shifts used A -> B, and Sn = (-s) mod N are the shifts used B -> A.
    Zero means the bi-circulant graph has diameter <= D.
    """
    total = 0
    for side in (0, 1):
        visA = 1 if side == 0 else 0
        visB = 1 if side == 1 else 0
        fA, fB = visA, visB
        for _ in range(D):
            nB = 0
            for s in Sp:
                nB |= _rot(fA, s, N, full)
            nB &= full & ~visB
            nA = 0
            for s in Sn:
                nA |= _rot(fB, s, N, full)
            nA &= full & ~visA
            if not (nA or nB):
                break
            visA |= nA
            visB |= nB
            fA, fB = nA, nB
        total += 2 * N - visA.bit_count() - visB.bit_count()
    return total


def _search_cyclic(N, d, D, rng, deadline, iters):
    """Simulated annealing over connection sets S (0 fixed in S, WLOG).

    Returns a valid S (diameter <= D) or None.
    """
    full = (1 << N) - 1

    def cost(S):
        return _unreached(N, S, [(N - s) % N for s in S], D, full)

    S = [0] + rng.sample(range(1, N), d - 1)
    cur = cost(S)
    if cur == 0:
        return S
    T0 = 2.0 + 0.1 * cur
    for step in range(iters):
        if time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.05
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = cost(S2)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur == 0:
                return S
    return None


def _bicirculant_edges(N, S):
    """Edges of the bi-circulant graph: A_x = x, B_y = N + y, A_x ~ B_{x+s}."""
    return [(x, N + (x + s) % N) for x in range(N) for s in S]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

ANNEAL_ITERS = 6000   # annealing steps per candidate order N


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D}: bipartite, 2-regular, diameter D.
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 and meets the Moore bound for D = 2.
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

    # Bi-circulant search: an order-2N candidate needs N in [lo, moore // 2].
    half_moore = moore // 2
    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > half_moore:
            break
        window = max(2, min(8, lo // 20))
        N = lo + rng.randrange(window)
        N = max(N, d)
        N = min(N, half_moore)
        S = _search_cyclic(N, d, D, rng, deadline, ANNEAL_ITERS)
        if S is not None:
            consider(2 * N, _bicirculant_edges(N, S))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
