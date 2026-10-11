"""Bold variant for the weak d=5, D=5 target: abelian Haar (bi-Cayley over Z_N) lifts.

Haar graph H(N, S): A_x ~ B_{x+s} for s in S, with 0 in S WLOG (translation of B).
It is d-regular and bipartite with 2N vertices. Because A-side and B-side are each
transitive and the two sides are swapped by an isomorphism, the diameter is exactly
the eccentricity of A_0. Distance sets are computed with N-bit integer bitmasks, where
rotation by s is a shift-and-or. That makes each evaluation very cheap, so we can
hill-climb over connection sets for orders N above the parent's record.

Fallbacks: K_{d,d} (D=2), the cycle C_{2D} (d=2), and the projective-plane incidence
graph for D=3. Every candidate is checked with lib.is_valid before it is accepted.
"""
import math
import random
import time

import lib

_FAIL_LIMIT = 6  # stop the ascending order sweep after this many consecutive failures


def _unc(N, S, D, FULL):
    """Number of (A or B) vertices of H(N, S) not within distance D of A_0."""
    seen_a = 1
    seen_b = 0
    front = 1
    on_a = True
    for _ in range(D):
        new = 0
        if on_a:
            # A -> B: A_x ~ B_{x+s}, so the new B set is the union of rotations by +s.
            for s in S:
                new |= ((front << s) | (front >> (N - s))) & FULL
            new &= ~seen_b
            seen_b |= new
        else:
            # B -> A: B_y ~ A_{y-s}, so the new A set is the union of rotations by -s.
            for s in S:
                t = (N - s) % N
                new |= ((front << t) | (front >> (N - t))) & FULL
            new &= ~seen_a
            seen_a |= new
        front = new
        on_a = not on_a
        if not front:
            break
    return 2 * N - seen_a.bit_count() - seen_b.bit_count()


def _find_S(N, d, D, rng, end):
    """Hill-climb with restarts for a connection set S (0 in S) with zero uncovered vertices."""
    FULL = (1 << N) - 1
    while time.monotonic() < end:
        S = [0] + rng.sample(range(1, N), d - 1)
        cur = _unc(N, S, D, FULL)
        stall = 0
        while cur and stall < 2500 and time.monotonic() < end:
            i = rng.randrange(1, d)
            c = rng.randrange(1, N)
            if c in S:
                stall += 1
                continue
            S2 = S[:]
            S2[i] = c
            v = _unc(N, S2, D, FULL)
            if v <= cur or rng.random() < math.exp(-(v - cur) / 1.0):
                if v < cur:
                    stall = 0
                else:
                    stall += 1
                S, cur = S2, v
            else:
                stall += 1
        if cur == 0:
            return sorted(S)
    return None


def _cyclic_search(d, D, rng, deadline, lo, hi):
    """Sweep N upward from lo; return (N, S) for the largest order that succeeded."""
    best = None
    N = lo
    fails = 0
    while N <= hi and fails < _FAIL_LIMIT:
        now = time.monotonic()
        if now >= deadline:
            break
        remaining = deadline - now
        end = min(deadline, now + min(4.0, max(0.5, 0.15 * remaining)))
        S = _find_S(N, d, D, rng, end)
        if S is not None:
            best = (N, S)
            fails = 0
        else:
            fails += 1
        N += 1
    return best


def _haar_edges(N, S):
    """Edges of H(N, S): A_x = x, B_y = N + y."""
    return [(x, N + (x + s) % N) for x in range(N) for s in S]


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and order 2d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best
    if d == 2:
        # Cycle C_{2D}: bipartite, 2-regular, diameter D.
        return lib.haar_graph(D, [0, 1])

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if best[0] < moore:
        hi = moore // 2
        lo = max(d, best[0] // 2 + 1)
        if lo <= hi:
            res = _cyclic_search(d, D, rng, deadline, lo, hi)
            if res is not None:
                N, S = res
                consider(2 * N, _haar_edges(N, S))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
