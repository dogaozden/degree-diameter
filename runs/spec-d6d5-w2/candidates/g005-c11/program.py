"""Targeted rewrite for the weakest case (d=6, D=5).

New family for D >= 3, d >= 3: random d-regular bipartite graphs on k+k vertices,
improved by simulated annealing over 2-switches (edge swaps that keep degrees and
bipartiteness) until the ordered count of pairs at distance > D is zero. The
search bisects on k, the number of vertices per side. Earlier safe families are
kept as fallbacks: K_{d,d}, the projective-plane incidence graph, and the
Araujo-Pardo-Lopez graph. Every returned graph passes lib.is_valid.

This code has not been executed. The annealing success rate at the target size is
unverified.
"""
import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _random_regular(k, d, rng):
    """Bipartite d-regular simple graph on k+k vertices as neighbour sets, or None.

    Built as d edge-disjoint permutation matchings, with local swaps to avoid repeats.
    """
    for _ in range(30):
        nbr = [set() for _ in range(k)]
        good = True
        for _r in range(d):
            p = list(range(k))
            rng.shuffle(p)
            for i in range(k):
                tries = 0
                while p[i] in nbr[i]:
                    tries += 1
                    if tries > 500:
                        break
                    j = rng.randrange(k)
                    if p[j] not in nbr[i] and p[i] not in nbr[j]:
                        p[i], p[j] = p[j], p[i]
                if p[i] in nbr[i]:
                    good = False
                    break
            if not good:
                break
            for i in range(k):
                nbr[i].add(p[i])
        if good:
            return nbr
    return None


def _build_adj(k, EA, EB):
    """Adjacency lists; left vertex a is a, right vertex b is k + b."""
    adj = [[] for _ in range(2 * k)]
    for a, b in zip(EA, EB):
        adj[a].append(k + b)
        adj[k + b].append(a)
    return adj


def _bad_ordered(n, adj, D):
    """Ordered count of (vertex, vertex) pairs at distance more than D (bitset BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal(k, d, D, rng, deadline):
    """Anneal 2-switches on a random d-regular bipartite graph with k vertices per side.

    Returns (n, edges) with zero bad pairs, or None if the deadline passes first.
    """
    nbr = _random_regular(k, d, rng)
    if nbr is None:
        return None
    EA, EB = [], []
    for i in range(k):
        for j in nbr[i]:
            EA.append(i)
            EB.append(j)
    keys = {a * k + b for a, b in zip(EA, EB)}
    m = len(EA)
    n = 2 * k
    cur = _bad_ordered(n, _build_adj(k, EA, EB), D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 0.2 + 3.0 * (1.0 - (now - start) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        a, b = EA[i], EB[i]
        c, e = EA[j], EB[j]
        if a == c or b == e:
            continue
        if a * k + e in keys or c * k + b in keys:
            continue
        # 2-switch: (a,b),(c,e) -> (a,e),(c,b). Degrees and bipartiteness are preserved.
        EB[i], EB[j] = e, b
        new = _bad_ordered(n, _build_adj(k, EA, EB), D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            keys.discard(a * k + b)
            keys.discard(c * k + e)
            keys.add(a * k + e)
            keys.add(c * k + b)
            cur = new
        else:
            EB[i], EB[j] = b, e
    if cur != 0:
        return None
    edges = [(a, k + b) for a, b in zip(EA, EB)]
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Annealed random-regular search, bisecting on k (vertices per side).
    if d >= 3 and D >= 3 and best_n < moore:
        half = moore // 2
        ok_k = best_n // 2
        fail_k = half + 1
        k = max(int(0.42 * half), d, ok_k + 1)
        step = 8
        while time.monotonic() < deadline - 0.5 and fail_k - ok_k > 1:
            if k <= ok_k or k >= fail_k:
                k = (ok_k + fail_k) // 2
            now = time.monotonic()
            rem = deadline - now
            slice_end = now + max(4.0, 0.35 * rem)
            res = _anneal(k, d, D, rng, min(deadline, slice_end))
            if res is not None:
                consider(res[0], res[1])
                ok_k = max(ok_k, k)
                k = k + step
            else:
                fail_k = min(fail_k, k)
                step = max(1, step // 2)
                k = (ok_k + fail_k) // 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
