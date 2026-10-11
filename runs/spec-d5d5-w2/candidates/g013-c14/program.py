import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: instead of algebraic lifts, search directly over balanced
# bipartite graphs made of d "perfect matchings" between two sides of size s.
#
#   A_i ~ B_{p_k(i)}  for k = 0..d-1, i = 0..s-1
#
# Each swap of two images inside one permutation keeps every vertex within
# degree d (duplicate edges only lower degree). The cost is the number of
# unordered vertex pairs at distance > D, computed with bitset balls. Simulated
# annealing drives the cost to zero for growing s. Every accepted graph is
# verified with lib.is_valid before it replaces the incumbent, so the output
# is always a valid graph (K_{d,d} fallback, or PG(2, d-1) when D = 3).
# ----------------------------------------------------------------------------


def _adjacency(s, perms):
    """Adjacency lists for the bipartite graph A = 0..s-1, B = s..2s-1."""
    adj_a = [set() for _ in range(s)]
    adj_b = [set() for _ in range(s)]
    for p in perms:
        for i in range(s):
            j = p[i]
            adj_a[i].add(j)
            adj_b[j].add(i)
    adj = [[s + j for j in a] for a in adj_a]
    adj.extend(list(b) for b in adj_b)
    return adj


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance greater than D (unreachable counts)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    total = 0
    for x in reach:
        total += n - x.bit_count()
    return total // 2


def _anneal(s, d, D, rng, deadline):
    """Anneal d permutations on s + s vertices until every pair is within distance D.

    Returns (n, edges) on success, or None if the deadline passes first.
    """
    n = 2 * s
    perms = []
    for _ in range(d):
        p = list(range(s))
        rng.shuffle(p)
        perms.append(p)
    cur = _bad_pairs(n, _adjacency(s, perms), D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    t0, t1 = 2.0, 0.15

    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - start) / span
        temp = t0 * (t1 / t0) ** frac

        k = rng.randrange(d)
        i = rng.randrange(s)
        j = rng.randrange(s)
        if i == j:
            continue
        p = perms[k]
        p[i], p[j] = p[j], p[i]
        new = _bad_pairs(n, _adjacency(s, perms), D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = new
        else:
            p[i], p[j] = p[j], p[i]

    edges = set()
    for p in perms:
        for i in range(s):
            edges.add((i, s + p[i]))
    return n, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Algebraic baseline for D = 3 when d - 1 is a prime power (meets the Moore bound).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)

    # Already optimal: return immediately (calibration cases).
    if best[0] >= moore:
        return best

    ok_s = max(d, best[0] // 2)
    step = max(1, ok_s // 8)
    cand = ok_s + step
    fails = 0

    while time.monotonic() < deadline and 2 * cand <= moore:
        remaining = deadline - time.monotonic()
        slice_t = max(1.0, remaining * (0.3 if fails == 0 else 0.5))
        slice_end = min(deadline, time.monotonic() + slice_t)
        res = _anneal(cand, d, D, rng, slice_end)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res
            ok_s = cand
            fails = 0
            cand = ok_s + step
        else:
            fails += 1
            if step > 1:
                step = max(1, step // 2)
            cand = ok_s + step

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
