import math
import random
import time

import lib


def _pg_start(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d, as (q, m, pairs)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            n, edges = lib.projective_plane_incidence(q)
            m = n // 2
            pairs = [(u, v - m) for u, v in edges]  # (point index, line index)
            return q, m, pairs
    return None


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (bitmask ball growth)."""
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


def _rem(adj, u, v):
    adj[u].discard(v)
    adj[v].discard(u)


def _add(adj, u, v):
    adj[u].add(v)
    adj[v].add(u)


def _flip(adj, a, b, c, e, forward):
    """Double-edge swap: (a,b),(c,e) -> (a,e),(c,b); reverse when forward is False."""
    if forward:
        _rem(adj, a, b)
        _rem(adj, c, e)
        _add(adj, a, e)
        _add(adj, c, b)
    else:
        _rem(adj, a, e)
        _rem(adj, c, b)
        _add(adj, a, b)
        _add(adj, c, e)


def _from_pairs(M, pairs):
    """Adjacency sets for a bipartite graph: A = 0..M-1, B = M..2M-1, pairs are (a, b_index)."""
    adj = [set() for _ in range(2 * M)]
    for a, bi in pairs:
        _add(adj, a, M + bi)
    return adj


def _fill(M, d, adj, rng, passes=3):
    """Greedily add edges between deficient opposite-side vertices, keeping degree <= d."""
    for _ in range(passes):
        A = [a for a in range(M) if len(adj[a]) < d]
        B = [M + b for b in range(M) if len(adj[M + b]) < d]
        if not A or not B:
            break
        rng.shuffle(A)
        rng.shuffle(B)
        added = 0
        for a in A:
            for b in B:
                if len(adj[a]) >= d:
                    break
                if len(adj[b]) < d and b not in adj[a]:
                    _add(adj, a, b)
                    added += 1
        if added == 0:
            break


def _anneal(M, d, D, adj, rng, deadline):
    """Anneal double-edge swaps (degree-preserving) to drive the bad-pair count to zero."""
    n = 2 * M
    E = [(a, b) for a in range(M) for b in adj[a]]
    cost = _bad(n, adj, D)
    T = 1.0
    while cost > 0 and time.monotonic() < deadline and len(E) >= 2:
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        _flip(adj, a, b, c, e, True)
        new = _bad(n, adj, D)
        if new <= cost or rng.random() < math.exp((cost - new) / T):
            cost = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            _flip(adj, a, b, c, e, False)
        T = max(0.2, T * 0.9995)
    return adj if cost == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and max degree d.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Plain projective plane incidence graph: diameter 3, valid for any D >= 3.
    st = _pg_start(d)
    if st is None:
        return best
    q, m, pairs = st
    n0, e0 = lib.projective_plane_incidence(q)
    consider(n0, e0)

    # Moore bound for bipartite graphs: 2 * sum_{i<D} (d-1)^i, so M <= moore / 2.
    moore = 2 * sum((d - 1) ** i for i in range(D))

    # Bipartite local search: grow the side size one step at a time, starting from
    # the projective plane, and repair bad pairs with degree-preserving swaps.
    M = m
    cur_pairs = list(pairs)
    while time.monotonic() < deadline:
        M += 1
        if 2 * M > moore:
            break
        adj = _from_pairs(M, cur_pairs)
        _fill(M, d, adj, rng)
        res = _anneal(M, d, D, adj, rng, deadline)
        if res is None:
            break
        cur_pairs = [(a, b - M) for a in range(M) for b in res[a]]
        consider(2 * M, [(a, M + bi) for a, bi in cur_pairs])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
