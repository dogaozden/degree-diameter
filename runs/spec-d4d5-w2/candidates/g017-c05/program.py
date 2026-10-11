import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bipartite switch annealing.
#
# Work on a d-regular bipartite graph with sides A = 0..s-1 and B = s..2s-1.
# Start from a circulant d-regular graph, then apply degree-preserving 2-switches
#   (a1,b1),(a2,b2) -> (a1,b2),(a2,b1)
# which keep the graph bipartite and d-regular. The cost is the number of
# unordered vertex pairs at distance > D, computed with bitmask balls.
# Cost 0 means a valid graph with diameter <= D.
# ----------------------------------------------------------------------------

def _build_adj(N, s, ea, eb):
    adj = [[] for _ in range(N)]
    for a, b in zip(ea, eb):
        adj[a].append(s + b)
        adj[s + b].append(a)
    return adj


def _cost(N, adj, D):
    """Number of ordered (vertex, vertex) pairs at distance > D (each unordered pair counted twice)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        if new == reach:
            break
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _anneal(s, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph with s vertices per side to diameter <= D.

    Returns (n, edges) on success, None if the deadline passes first.
    """
    N = 2 * s
    ea, eb = [], []
    for i in range(s):
        for t in range(d):
            ea.append(i)
            eb.append((i + t) % s)
    E = len(ea)
    pairs = set(zip(ea, eb))
    adj = _build_adj(N, s, ea, eb)
    cost = _cost(N, adj, D)
    if cost == 0:
        return N, [(a, s + b) for a, b in zip(ea, eb)]

    T0 = max(0.5, 0.03 * cost)
    T1 = 0.2
    t_start = time.monotonic()
    span = max(1e-9, deadline - t_start)

    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - t_start) / span)
        T = T0 * (T1 / T0) ** frac

        e1 = rng.randrange(E)
        e2 = rng.randrange(E)
        if e1 == e2:
            continue
        a1, b1 = ea[e1], eb[e1]
        a2, b2 = ea[e2], eb[e2]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in pairs or (a2, b1) in pairs:
            continue

        # Apply the switch.
        eb[e1], eb[e2] = b2, b1
        pairs.discard((a1, b1))
        pairs.discard((a2, b2))
        pairs.add((a1, b2))
        pairs.add((a2, b1))

        adj = _build_adj(N, s, ea, eb)
        c2 = _cost(N, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                return N, [(a, s + b) for a, b in zip(ea, eb)]
        else:
            # Revert.
            eb[e1], eb[e2] = b1, b2
            pairs.discard((a1, b2))
            pairs.discard((a2, b1))
            pairs.add((a1, b1))
            pairs.add((a2, b2))
    return None


# ----------------------------------------------------------------------------
# Structured candidates.
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + max(1.0, 0.8 * time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        m = 2 * D
        return m, [(i, (i + 1) % m) for i in range(m)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2

    # Safe fallback: K_{d,d}.
    best_n, best_e = lib.haar_graph(d, range(d))

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
            return pg
        return best_n, best_e

    # D >= 4: ramp the side size upward with annealing from a circulant start.
    # Every success is a valid graph, so the best one found is always kept.
    s_next = best_n // 2 + 1
    while True:
        remaining = end - time.monotonic()
        if remaining < 0.5:
            break
        cap = remaining if remaining < 3.0 else max(2.0, 0.25 * remaining)
        res = _anneal(s_next, d, D, rng, time.monotonic() + cap)
        if res is not None:
            n, e = res
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_e = n, e
                s_next += 1
                continue
        # Failed or invalid: retry the same size with a fresh random walk.

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
