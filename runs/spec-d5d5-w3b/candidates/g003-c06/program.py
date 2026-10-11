import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy: a different family from the parent's voltage/bi-Cayley lifts.
#
# We anneal directly over bipartite graphs with a fixed side size N. Every
# move is a degree-preserving 2-switch, so degrees stay <= d and the graph
# stays bipartite. The cost is the number of ordered vertex pairs at distance
# greater than D, computed with bitmask balls. N grows whenever annealing
# reaches cost zero.
#
# Safe fallbacks: K_{d,d} (diameter 2, Moore-optimal for D = 2) and the
# projective-plane incidence graph for D = 3. Every result is checked with
# lib.is_valid before it replaces the current best.
# ----------------------------------------------------------------------------

MIN_SLICE = 4.0     # seconds for one annealing attempt (lower bound)
MAX_SLICE_FRAC = 0.4  # fraction of remaining time given to one attempt


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost(adj, N, D):
    """Ordered pairs (u, v) with distance > D. Zero means the graph has diameter <= D."""
    n2 = 2 * N
    reach = [1 << v for v in range(n2)]
    for _ in range(D):
        new = [0] * n2
        changed = False
        for v in range(n2):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
            if r != reach[v]:
                changed = True
        reach = new
        if not changed:
            break
    full = n2
    return sum(full - r.bit_count() for r in reach)


def _anneal_attempt(N, d, D, rng, deadline):
    """Anneal a d-regular-ish bipartite graph on sides of size N. Return edge list or None."""
    S = set()
    edges = []
    for _ in range(d):
        p = list(range(N))
        for _try in range(30):
            rng.shuffle(p)
            if all((i * N + p[i]) not in S for i in range(N)):
                break
        for i in range(N):
            key = i * N + p[i]
            if key not in S:
                S.add(key)
                edges.append([i, p[i]])

    adj = [[] for _ in range(2 * N)]
    for a, b in edges:
        adj[a].append(N + b)
        adj[N + b].append(a)

    cost = _cost(adj, N, D)
    m = len(edges)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        temp = max(0.2, 3.0 * (1.0 - frac))

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = edges[i]
        a2, b2 = edges[j]
        if a1 == a2 or b1 == b2:
            continue
        k1 = a1 * N + b2
        k2 = a2 * N + b1
        if k1 in S or k2 in S:
            continue

        # Apply the 2-switch in place.
        adj[a1].remove(N + b1)
        adj[N + b1].remove(a1)
        adj[a2].remove(N + b2)
        adj[N + b2].remove(a2)
        adj[a1].append(N + b2)
        adj[N + b2].append(a1)
        adj[a2].append(N + b1)
        adj[N + b1].append(a2)

        c2 = _cost(adj, N, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = c2
            S.discard(a1 * N + b1)
            S.discard(a2 * N + b2)
            S.add(k1)
            S.add(k2)
            edges[i] = [a1, b2]
            edges[j] = [a2, b1]
        else:
            # Revert the adjacency change.
            adj[a1].remove(N + b2)
            adj[N + b2].remove(a1)
            adj[a2].remove(N + b1)
            adj[N + b1].remove(a2)
            adj[a1].append(N + b1)
            adj[N + b1].append(a1)
            adj[a2].append(N + b2)
            adj[N + b2].append(a2)

    if cost == 0:
        return [(a, N + b) for a, b in edges]
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # lo is the largest side size N with a verified graph on 2N vertices.
    lo = best[0] // 2
    step = 4
    while best[0] < moore and time.monotonic() < deadline - 0.5:
        N = max(lo + step, d)
        if 2 * N > moore:
            N = moore // 2
            if N <= lo:
                break
        remaining = deadline - time.monotonic()
        slice_len = max(MIN_SLICE, min(remaining, MAX_SLICE_FRAC * remaining))
        slice_end = min(deadline, time.monotonic() + slice_len)

        edges = _anneal_attempt(N, d, D, rng, slice_end)
        if edges is not None and consider(2 * N, edges):
            lo = N
            step = min(2 * step, 16)
        else:
            step = max(1, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
