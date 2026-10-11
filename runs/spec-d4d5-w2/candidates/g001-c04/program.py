import math
import random
import time

import lib


def _unreached(m, S, D):
    """Count (vertex, source) pairs not within distance D of a_0 or b_0 in Haar(m, S).

    Haar graphs of Z_m are invariant under translation, so distances from a_0 and b_0
    cover every pair. The result is 0 exactly when the diameter is at most D (and the graph is connected).
    """
    N = 2 * m
    total = 0
    for src in (0, m):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        reached = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < m:  # a_i is adjacent to b_{i+s}
                    for s in S:
                        w = m + (v + s) % m
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:      # b_j is adjacent to a_{j-s}
                    j = v - m
                    for s in S:
                        w = (j - s) % m
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            if not nxt:
                break
            reached += len(nxt)
            frontier = nxt
        total += N - reached
    return total


def _search(m, d, D, rng, end):
    """Local search for a connection set S (0 in S, |S| = d) in Z_m with Haar(m, S) of diameter <= D.

    Simulated annealing on the number of unreached pairs. Returns sorted S, or None if time runs out.
    """
    def fresh():
        return [0] + rng.sample(range(1, m), d - 1)

    S = fresh()
    cur = _unreached(m, S, D)
    best_seen, stall = cur, 0
    T = 0.8
    while cur:
        if time.monotonic() >= end:
            return None
        if stall > 1500:  # restart from a random set after stagnation
            S = fresh()
            cur = _unreached(m, S, D)
            best_seen, stall = cur, 0
            continue
        i = rng.randrange(1, d)
        cand = rng.randrange(1, m)
        if cand in S:
            stall += 1
            continue
        new = S[:]
        new[i] = cand
        c = _unreached(m, new, D)
        if c <= cur or rng.random() < math.exp((cur - c) / T):
            S, cur = new, c
        if cur < best_seen:
            best_seen, stall = cur, 0
        else:
            stall += 1
    return sorted(S)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    # Safe fallback: K_{d,d}, or a single vertex if that is not valid for D.
    fallback = (1, [])
    kdd = lib.haar_graph(d, range(d)) if d >= 1 else (1, [])
    if lib.is_valid(kdd[0], kdd[1], d, D):
        fallback = kdd

    # D = 3 with d-1 a prime power: the projective plane incidence graph is optimal.
    if D == 3 and lib.is_prime_power(d - 1):
        n, edges = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, edges, d, D):
            return n, edges

    # D <= 2 or d < 2: K_{d,d} (or the fallback) is already optimal or trivial.
    if D <= 2 or d < 2:
        return fallback

    rng = random.Random(seed)
    best = fallback
    m = d + 1
    fails = 0
    while time.monotonic() < deadline and fails < 6:
        remaining = deadline - time.monotonic()
        end = time.monotonic() + max(0.5, 0.12 * remaining)
        end = min(end, deadline)
        S = _search(m, d, D, rng, end)
        if S is not None:
            n, edges = lib.haar_graph(m, S)
            if lib.is_valid(n, edges, d, D) and n > best[0]:
                best = (n, edges)
            fails = 0
            m += 1
        else:
            fails += 1
            m += 1
    return best
