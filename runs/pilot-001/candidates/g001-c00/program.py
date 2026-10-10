import random
import time

import lib


def _two_root_bad(m, S, D):
    """Count vertices NOT within distance D of a_0 or b_0 in the Haar graph H(Z_m, S).

    Z_m acts transitively on each side by translation, so the graph has diameter <= D
    exactly when every vertex is within D of a_0 and of b_0. This two-source BFS
    certificate costs O(m*d) instead of the all-pairs check in lib.within_diameter.
    """
    bad = 0
    for root in (0, m):
        dist = {root: 0}
        frontier = [root]
        for depth in range(1, D + 1):
            nxt = []
            for v in frontier:
                if v < m:
                    for s in S:
                        w = m + (v + s) % m
                        if w not in dist:
                            dist[w] = depth
                            nxt.append(w)
                else:
                    j = v - m
                    for s in S:
                        w = (j - s) % m
                        if w not in dist:
                            dist[w] = depth
                            nxt.append(w)
            if not nxt:
                break
            frontier = nxt
        bad += 2 * m - len(dist)
    return bad


def _climb(m, d, D, rng, iters, t_end):
    """Repair search over connection sets S (0 in S, |S| = d) for a fixed Z_m.

    Starts from a random S and repeatedly replaces one non-zero shift with a new one,
    minimising the two-root uncovered count. Occasional uphill moves avoid stalling.
    Returns S with zero cost, or None.
    """
    S = [0] + rng.sample(range(1, m), d - 1)
    cost = _two_root_bad(m, S, D)
    for _ in range(iters):
        if cost == 0 or time.monotonic() > t_end:
            break
        i = rng.randrange(1, d)
        cand = rng.randrange(1, m)
        if cand in S:
            continue
        T = list(S)
        T[i] = cand
        c = _two_root_bad(m, T, D)
        if c <= cost or rng.random() < 0.02:
            S, cost = T, c
    return S if cost == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1:
        return 2, [(0, 1)]

    # Projective-plane incidence graph meets the Moore bound for D = 3.
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
    m = d + 1
    fails = 0
    while time.monotonic() < deadline and fails < 4:
        now = time.monotonic()
        remaining = deadline - now
        t_end = min(deadline, now + max(0.05, remaining / 5.0))
        S = _climb(m, d, D, rng, 250, t_end)
        if S is not None:
            n, edges = lib.haar_graph(m, S)
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)
            fails = 0
        else:
            fails += 1
        m += 1
    return best
