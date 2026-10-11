import math
import random
import time

import lib


# Haar graph H(m, S): a_i ~ b_{i+s} for s in S, on Z_m. Its translations and the
# side-swap a_i <-> b_{-i} are automorphisms, so one BFS from a_0 decides the
# diameter: the graph has diameter <= D iff a_0 reaches all 2m vertices within D.

def _cost(m, S, D):
    """Number of vertices NOT within distance D of a_0 in H(m, S)."""
    seen = [False] * (2 * m)
    seen[0] = True
    frontier = [0]
    cnt = 1
    for _ in range(D):
        nxt = []
        for v in frontier:
            if v < m:
                for s in S:
                    w = m + (v + s) % m
                    if not seen[w]:
                        seen[w] = True
                        nxt.append(w)
            else:
                j = v - m
                for s in S:
                    w = (j - s) % m
                    if not seen[w]:
                        seen[w] = True
                        nxt.append(w)
        cnt += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return 2 * m - cnt


def _climb(m, d, D, deadline, rng):
    """Simulated-annealing-style search for a d-subset S of Z_m with zero cost."""
    S = rng.sample(range(m), d)
    c = _cost(m, S, D)
    T = 0.5
    while c > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        x = rng.randrange(m)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _cost(m, S, D)
        if c2 <= c or rng.random() < math.exp((c - c2) / T):
            c = c2
        else:
            S[i] = old
        T = max(0.05, T * 0.9995)
    return list(S) if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.80 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best
    if d == 2:
        consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        return best

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    # D = 3, d-1 a prime power: projective plane incidence graph meets the bound.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        if best[0] >= moore:
            return best

    # Bold new construction: binary search on the cyclic Haar-lift order m,
    # with a randomized search for a connection set S of size d per m.
    m_hi = moore // 2          # order 2m must not exceed the Moore bound
    lo = max(best[0] // 2, d)
    hi = m_hi
    while lo < hi and time.monotonic() < deadline:
        mid = (lo + hi + 1) // 2
        remaining = deadline - time.monotonic()
        attempt_deadline = time.monotonic() + max(1.0, remaining * 0.3)
        S = _climb(mid, d, D, min(attempt_deadline, deadline), rng)
        if S is not None:
            n2, e2 = lib.haar_graph(mid, S)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
                lo = mid
            else:
                hi = mid - 1
        else:
            hi = mid - 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
