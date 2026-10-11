import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

ATTEMPT_SECS = 12.0    # wall-clock slice for one target order N
ANNEAL_ITERS = 3000    # edge-switch steps per attempt


# ----------------------------------------------------------------------------
# Structured baseline for D = 3: incidence graph of PG(2, q), q + 1 <= d.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Edge-switch annealing on bipartite d-regular graphs.
#
# Start from a bi-circulant graph (A_i -- B_{i+s} for s in a random d-subset of
# Z_N), which is simple and d-regular. Each move swaps the partners of two
# edges: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Degrees and bipartiteness are kept,
# and the cost is the number of vertex pairs at distance > D. Zero means valid.
# ----------------------------------------------------------------------------

def _cost(N, adj, D):
    """Unordered pairs at distance > D, via bitmask ball growth."""
    V = 2 * N
    reach = [1 << v for v in range(V)]
    for _ in range(D):
        new = [0] * V
        for v in range(V):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    total = 0
    for r in reach:
        total += V - r.bit_count()
    return total // 2


def _anneal(N, d, D, rng, deadline, iters):
    """Anneal a d-regular bipartite graph on N + N vertices to diameter <= D."""
    if N < d:
        return None
    S = rng.sample(range(N), d)
    E = [[i, (i + s) % N] for i in range(N) for s in S]
    eset = {a * N + b for a, b in E}

    def build_adj():
        adj = [[] for _ in range(2 * N)]
        for a, b in E:
            adj[a].append(N + b)
            adj[N + b].append(a)
        return adj

    cost = _cost(N, build_adj(), D)
    m = len(E)
    T0 = max(1.0, 0.02 * cost)
    T1 = 0.05

    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = T0 * (T1 / T0) ** (it / max(1, iters))

        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if a1 * N + b2 in eset or a2 * N + b1 in eset:
            continue

        E[i] = [a1, b2]
        E[j] = [a2, b1]
        eset.discard(a1 * N + b1)
        eset.discard(a2 * N + b2)
        eset.add(a1 * N + b2)
        eset.add(a2 * N + b1)

        c2 = _cost(N, build_adj(), D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = c2
        else:
            E[i] = [a1, b1]
            E[j] = [a2, b2]
            eset.discard(a1 * N + b2)
            eset.discard(a2 * N + b1)
            eset.add(a1 * N + b1)
            eset.add(a2 * N + b2)

    if cost != 0:
        return None
    return [(a, N + b) for a, b in E]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for every D >= 2 (diameter 2).
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    moore = lib.moore_bound(d, D)
    rng = random.Random(seed)

    # Adaptive search over the side size N (order 2N). After a success the
    # step doubles; after a failure it halves. Retries at the same N use fresh
    # randomness because each attempt draws a new connection set.
    good = max(d, best[0] // 2)
    step = max(1, good // 16)
    while time.monotonic() < deadline:
        N = good + step
        if 2 * N > moore:
            if step == 1:
                break
            step = max(1, step // 2)
            continue
        slice_end = min(deadline, time.monotonic() + ATTEMPT_SECS)
        edges = _anneal(N, d, D, rng, slice_end, ANNEAL_ITERS)
        if edges is not None:
            consider(2 * N, edges)
            good = N
            step *= 2
        else:
            step = max(1, step // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
