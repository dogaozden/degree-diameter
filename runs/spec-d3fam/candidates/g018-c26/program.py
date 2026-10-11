import math
import random
import time

import lib


def _bad_count(n, adj, D):
    """Ordered count of vertex pairs at distance > D, via bitmask BFS over adjacency sets."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _base(d, D):
    """Algebraic record-level base for D = 3, validated; None if unavailable."""
    if D != 3:
        return None
    q = d - 1
    cand = None
    if q >= 2 and lib.is_prime_power(q):
        cand = lib.projective_plane_incidence(q)
    elif d - 2 >= 3 and lib.is_prime_power(d - 2):
        cand = lib.araujo_lopez_graph(d - 2)
    if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
        return cand
    return None


def _anneal_regular(m, d, D, rng, deadline):
    """Search a d-regular bipartite graph on sides of size m (A = 0..m-1, B = m..2m-1) with diameter <= D.

    Start from a Haar-type circulant (simple, regular, bipartite), randomise with degree-preserving
    2-switches, then anneal on the number of ordered pairs at distance > D.
    Returns (2m, edges) or None if the deadline passes first.
    """
    n = 2 * m
    shifts = rng.sample(range(m), d)
    E = []
    for i in range(m):
        for s in shifts:
            E.append((i, m + (i + s) % m))
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)

    M = len(E)

    def try_switch(i, j):
        """Return (a, b, c, e) if the switch of edges i, j is legal, else None."""
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            return None
        return a, b, c, e

    def apply(a, b, c, e):
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)

    def undo(a, b, c, e):
        adj[a].discard(e); adj[e].discard(a)
        adj[c].discard(b); adj[b].discard(c)
        adj[a].add(b); adj[b].add(a)
        adj[c].add(e); adj[e].add(c)

    # Randomise the circulant while keeping it simple and regular.
    for _ in range(3 * M):
        i, j = rng.randrange(M), rng.randrange(M)
        if i == j:
            continue
        sw = try_switch(i, j)
        if sw is None:
            continue
        a, b, c, e = sw
        apply(a, b, c, e)
        E[i] = (a, e)
        E[j] = (c, b)

    cur = _bad_count(n, adj, D)
    T = 0.5
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        i, j = rng.randrange(M), rng.randrange(M)
        if i == j:
            continue
        sw = try_switch(i, j)
        if sw is None:
            continue
        a, b, c, e = sw
        apply(a, b, c, e)
        new = _bad_count(n, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            undo(a, b, c, e)
    return n, list(E)


def _haar_fallback(d, D, rng, deadline):
    """Random Haar graphs with growing modulus; always returns a valid graph."""
    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    base = _base(d, D)
    if base is None:
        fb = _haar_fallback(d, D, rng, deadline)
        if lib.is_valid(fb[0], fb[1], d, D):
            return fb
        return lib.haar_graph(d, range(d))

    best = base
    # Bold change for the hard D = 3 cases: search directly for regular bipartite graphs
    # on more vertices than the algebraic record, instead of growing by augmentation.
    if D == 3 and d >= 10:
        m = base[0] // 2 + 1
        while time.monotonic() < deadline:
            res = _anneal_regular(m, d, D, rng, deadline)
            if res is None:
                break
            if lib.is_valid(res[0], res[1], d, D):
                best = res
                m += 1
            else:
                break
    return best
