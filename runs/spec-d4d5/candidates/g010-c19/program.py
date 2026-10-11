import math
import random
import time

import lib


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance greater than D (bitmask ball growth)."""
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


def _rewire(adj, N, rem, add):
    """Remove the edges in `rem` and insert the edges in `add` (side-local (a, b) pairs)."""
    for a, b in rem:
        adj[a].remove(N + b)
        adj[N + b].remove(a)
    for a, b in add:
        adj[a].append(N + b)
        adj[N + b].append(a)


def _anneal(N, El, D, rng, deadline):
    """Simulated annealing over double-edge switches of a d-regular bipartite graph.

    Each switch replaces (a1,b1),(a2,b2) by (a1,b2),(a2,b1). This keeps every
    degree and the bipartition, so only the number of bad pairs is optimised.
    Returns the edge list when the diameter is <= D, otherwise None.
    """
    n = 2 * N
    El = list(El)
    E = set(El)
    adj = [[] for _ in range(n)]
    for a, b in El:
        adj[a].append(N + b)
        adj[N + b].append(a)
    cost = _bad_pairs(n, adj, D)
    if cost == 0:
        return El
    m = len(El)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0 = max(1.0, 0.05 * cost)
    T_end = 0.2
    while True:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = T0 * (T_end / T0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = El[i]
        a2, b2 = El[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in E or (a2, b1) in E:
            continue
        rem = [(a1, b1), (a2, b2)]
        add = [(a1, b2), (a2, b1)]
        _rewire(adj, N, rem, add)
        c2 = _bad_pairs(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            E.discard((a1, b1))
            E.discard((a2, b2))
            E.add((a1, b2))
            E.add((a2, b1))
            El[i] = (a1, b2)
            El[j] = (a2, b1)
            cost = c2
            if cost == 0:
                return El
        else:
            _rewire(adj, N, add, rem)


def _grow(N, El, d, rng):
    """Add one vertex to each side of a d-regular bipartite graph, keeping it d-regular.

    Pick d edges (a_i, b_i) with distinct endpoints, delete them, then join
    a new A vertex to every b_i and a new B vertex to every a_i.
    """
    order = list(range(len(El)))
    rng.shuffle(order)
    chosen = []
    ua, ub = set(), set()
    for i in order:
        a, b = El[i]
        if a in ua or b in ub:
            continue
        chosen.append((a, b))
        ua.add(a)
        ub.add(b)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    rem = set(chosen)
    newEl = [e for e in El if e not in rem]
    for a, b in chosen:
        newEl.append((N, b))
        newEl.append((a, N))
    return N + 1, newEl


def _global(N, El):
    """Convert side-local edges to the global labelling (A = 0..N-1, B = N..2N-1)."""
    return 2 * N, [(a, N + b) for a, b in El]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 0.5

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1 or D == 2:
        # K_{d,d} is optimal here: bipartite diameter 2 forces a complete bipartite graph.
        return lib.haar_graph(d, range(d))

    rng = random.Random(seed)

    # Safe fallback: K_{d,d}, which has diameter 2 and so is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    N, El = d, [(a, b) for a in range(d) for b in range(d)]

    try:
        # Start from PG(2, d-1) when d-1 is a prime power: it is d-regular with diameter 3.
        if d >= 3 and lib.is_prime_power(d - 1):
            n0, e0 = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n0, e0, d, D):
                best = (n0, e0)
                m = n0 // 2
                N, El = m, [(u, v - m) for u, v in e0]

        # Warm-started growth: add one vertex per side, then anneal back to diameter <= D.
        while time.monotonic() < deadline:
            found = None
            for _attempt in range(3):
                now = time.monotonic()
                remaining = deadline - now
                if remaining <= 0:
                    break
                g = _grow(N, El, d, rng)
                if g is None:
                    break
                N2, El2 = g
                res = _anneal(N2, El2, D, rng, now + max(0.05, 0.35 * remaining))
                if res is not None:
                    found = (N2, res)
                    break
            if found is None:
                break
            N, El = found
            n2, e2 = _global(N, El)
            if lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
            else:
                break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
