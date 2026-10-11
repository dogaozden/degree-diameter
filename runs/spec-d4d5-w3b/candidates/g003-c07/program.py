"""Degree-preserving 2-switch annealing for bipartite graphs with diameter D.

New idea (not in the parent): instead of lifting a small base graph, start from a
random d-regular bipartite graph on k + k vertices and anneal it with degree-preserving
2-switches. A switch replaces edges (a,b), (c,e) by (a,e), (c,b), which keeps every
degree and keeps the graph bipartite. The cost is the number of vertex pairs farther
than D apart, computed with bitsets. The order k grows along a ladder: every time an
annealing run reaches cost 0, the next, slightly larger k is tried.
"""
import math
import random
import time

import lib


def _bad(n, adj, D):
    """Number of unordered pairs at distance more than D (bitset ball growth)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _init(k, d, rng):
    """Union of d random perfect matchings between sides A = 0..k-1 and B = k..2k-1, without repeated edges."""
    E = set()
    for _ in range(d):
        for _attempt in range(2000):
            perm = list(range(k, 2 * k))
            rng.shuffle(perm)
            pairs = [(a, perm[a]) for a in range(k)]
            if all(p not in E for p in pairs):
                E.update(pairs)
                break
        else:
            return None
    return list(E)


def _set(E, S, adj, i, old, new):
    """Replace edge E[i] = old by new, keeping the edge set and adjacency lists in sync."""
    E[i] = new
    S.discard(old)
    S.add(new)
    adj[old[0]].remove(old[1])
    adj[old[1]].remove(old[0])
    adj[new[0]].append(new[1])
    adj[new[1]].append(new[0])


def _sa(k, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on 2k vertices toward diameter <= D. Returns edges or None."""
    n = 2 * k
    E = _init(k, d, rng)
    if E is None:
        return None
    S = set(E)
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    cost = _bad(n, adj, D)
    if cost == 0:
        return E

    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0 = max(1.0, 0.02 * cost)
    T1 = 0.1
    temp = T0
    m = len(E)
    it = 0
    while True:
        it += 1
        if (it & 7) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            temp = T0 * (T1 / T0) ** ((now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        n1 = (a, e)
        n2 = (c, b)
        if n1 in S or n2 in S:
            continue
        _set(E, S, adj, i, (a, b), n1)
        _set(E, S, adj, j, (c, e), n2)
        c2 = _bad(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = c2
            if cost == 0:
                return list(E)
        else:
            _set(E, S, adj, i, n1, (a, b))
            _set(E, S, adj, j, n2, (c, e))
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    # K_{d,d}: valid fallback for every D >= 2 (and d = 1).
    if D == 2 or d == 1:
        return lib.haar_graph(d, range(d))

    # Fast path: projective plane meets the Moore bound when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    best = lib.haar_graph(d, range(d))
    best_k = d
    step = max(1, best_k // 12)

    # Size ladder: try to grow k (side size), each time annealing from a fresh random start.
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.5:
            break
        cand = best_k + step
        budget = min(remaining, max(2.0, 0.3 * remaining))
        E = _sa(cand, d, D, rng, now + budget)
        if E is not None:
            n = 2 * cand
            if lib.is_valid(n, E, d, D):
                best = (n, E)
                best_k = cand
                step = max(1, best_k // 12)
                continue
        if step > 1:
            step = 1
            continue
        break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
