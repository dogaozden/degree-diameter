import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Direct simulated annealing over d-regular bipartite graphs.
#
# State: a d-regular bipartite graph on h + h vertices (left 0..h-1, right h..2h-1),
# stored as an edge list. Moves are double-edge swaps, which keep every degree
# equal to d and keep the graph bipartite and simple. Cost is the number of
# unordered vertex pairs at distance > D (unreachable pairs included). A cost of
# zero is a valid graph of order 2h.
# ----------------------------------------------------------------------------

def _bad_pairs(N, adj, D):
    """Number of unordered pairs with distance > D, via bitmask BFS balls."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _set_edge(E, eset, adj, i, na, nb):
    """Replace edge index i with (na, nb), keeping eset and adjacency lists in sync."""
    oa, ob = E[i]
    eset.discard((oa, ob))
    eset.add((na, nb))
    adj[oa].remove(ob)
    adj[ob].remove(oa)
    adj[na].append(nb)
    adj[nb].append(na)
    E[i] = [na, nb]


def _anneal(h, d, D, rng, end):
    """Anneal a d-regular bipartite graph on 2h vertices until its cost is zero or time runs out.

    Returns the edge list of a valid graph, or None.
    """
    N = 2 * h
    # Circulant start: a connects to h + (a + s) mod h for s in S (distinct shifts).
    S = rng.sample(range(h), d)
    adj = [[] for _ in range(N)]
    E = []
    eset = set()
    for a in range(h):
        for s in S:
            b = h + (a + s) % h
            E.append([a, b])
            eset.add((a, b))
            adj[a].append(b)
            adj[b].append(a)

    cur = _bad_pairs(N, adj, D)
    t0 = time.monotonic()
    span = max(1e-6, end - t0)
    m = len(E)

    while cur > 0:
        now = time.monotonic()
        if now >= end:
            break
        frac = (now - t0) / span
        T = 1.0 * (0.02 ** frac)

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue

        _set_edge(E, eset, adj, i, a1, b2)
        _set_edge(E, eset, adj, j, a2, b1)
        c2 = _bad_pairs(N, adj, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
        else:
            _set_edge(E, eset, adj, j, a2, b2)
            _set_edge(E, eset, adj, i, a1, b1)

    if cur == 0:
        return [(a, b) for a, b in E]
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Projective plane incidence graph: diameter 3, meets the Moore bound when d-1 is a prime power.
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)

    # Time budget: leave a clear margin under time_limit.
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 5))

    rng = random.Random(seed * 1000003 + d * 31 + D)
    moore = lib.moore_bound(d, D)

    # Climb: find d-regular bipartite graphs of increasing half-size h.
    target = max(d + 1, best_n // 2 + 1)
    while time.monotonic() < deadline and 2 * target <= moore:
        now = time.monotonic()
        remaining = deadline - now
        chunk_end = min(deadline, now + max(1.5, 0.3 * remaining))
        edges = _anneal(target, d, D, rng, chunk_end)
        if edges is not None and lib.is_valid(2 * target, edges, d, D):
            if 2 * target > best_n:
                best_n, best_e = 2 * target, edges
            target += 1

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
