import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Exact baseline: incidence graph of PG(2, q), q the largest prime power with q+1 <= d.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW construction: unstructured d-regular bipartite graphs repaired by search.
#
# Start from a circulant bipartite graph A_a ~ B_{(a+t) mod s} for d distinct shifts t
# (simple and d-regular), mix it with random 2-switches (which keep the graph simple,
# d-regular and bipartite), then run simulated annealing on 2-switches to minimise the
# number of vertex pairs at distance > D. The graph has n = 2s vertices, sides A and B
# of size s. Every accepted state is d-regular, so degree stays <= d.
# ----------------------------------------------------------------------------

def _adj_from_edges(n, ea, eb, s):
    adj = [[] for _ in range(n)]
    for a, b in zip(ea, eb):
        adj[a].append(s + b)
        adj[s + b].append(a)
    return adj


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D, via bitmask balls."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _repair(d, D, s, rng, end):
    """Try to find a valid d-regular bipartite graph with s vertices per side; None on timeout."""
    n = 2 * s
    shifts = rng.sample(range(s), d)
    ea, eb = [], []
    for a in range(s):
        for t in shifts:
            ea.append(a)
            eb.append((a + t) % s)
    m = len(ea)
    adjA = [set() for _ in range(s)]
    for a, b in zip(ea, eb):
        adjA[a].add(b)

    def can_switch(i, j):
        a1, b1 = ea[i], eb[i]
        a2, b2 = ea[j], eb[j]
        return not (a1 == a2 or b1 == b2 or b2 in adjA[a1] or b1 in adjA[a2])

    def switch(i, j):
        # Replace (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Applying it twice undoes it.
        a1, b1 = ea[i], eb[i]
        a2, b2 = ea[j], eb[j]
        adjA[a1].discard(b1)
        adjA[a2].discard(b2)
        adjA[a1].add(b2)
        adjA[a2].add(b1)
        eb[i] = b2
        eb[j] = b1

    for _ in range(4 * m):
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i != j and can_switch(i, j):
            switch(i, j)

    cur = _bad_pairs(n, _adj_from_edges(n, ea, eb, s), D)
    while cur > 0:
        if time.monotonic() > end:
            return None
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j or not can_switch(i, j):
            continue
        switch(i, j)
        new = _bad_pairs(n, _adj_from_edges(n, ea, eb, s), D)
        T = 0.5
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            switch(i, j)
    edges = [(a, s + b) for a, b in zip(ea, eb)]
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 2:
        return best

    rng = random.Random(seed)
    mo = lib.moore_bound(d, D)
    # Heuristic starting size: a bit above the record ratio observed for d=7, D=5.
    s0 = max(d, int(0.372 * mo) // 2 + 1)

    best_s = 0
    fail_s = None
    s = s0
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 2.0 or s < d:
            break
        slice_end = now + 0.6 * remaining
        res = _repair(d, D, s, rng, slice_end)
        if res is not None:
            consider(res[0], res[1])
            best_s = max(best_s, s)
            if fail_s is None:
                s = best_s + max(2, best_s // 60)
            else:
                if fail_s - best_s <= 1:
                    break
                s = (best_s + fail_s) // 2
        else:
            fail_s = s if fail_s is None else min(fail_s, s)
            if best_s == 0:
                s = s - max(2, s // 20)
            else:
                if fail_s - best_s <= 1:
                    break
                s = (best_s + fail_s) // 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
