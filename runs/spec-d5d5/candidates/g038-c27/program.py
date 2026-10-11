import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Direct simulated annealing over bi-regular bipartite graphs.
#
# Instead of searching voltage lifts, this works on the whole graph. The state
# is a d-regular bipartite multigraph-free edge list on parts A = 0..N-1 and
# B = 0..N-1. Each move is an edge switch (a1,b1),(a2,b2) -> (a1,b2),(a2,b1),
# which keeps all degrees and bipartiteness. The cost is the number of
# unordered vertex pairs at distance greater than D. Cost 0 gives a valid graph.
# ----------------------------------------------------------------------------

def _kdd(d):
    """Fallback K_{d,d}: order 2d, diameter 2."""
    return lib.haar_graph(d, range(d))


def _pg_if_optimal(d, D):
    """Moore-optimal PG(2, d-1) incidence graph for D = 3 when d-1 is a prime power."""
    if D == 3 and d >= 2 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    return None


def _random_bireg(N, d, rng, tries=2000):
    """Random d-regular bipartite edge list on N+N vertices, simple if possible."""
    A = [a for a in range(N) for _ in range(d)]
    B = [b for b in range(N) for _ in range(d)]
    last = []
    for _ in range(tries):
        rng.shuffle(B)
        E = list(zip(A, B))
        if len(set(E)) == len(E):
            return E
        last = E
    return list(dict.fromkeys(last))  # rare fallback: unique edges only


def _cost(N, D, E):
    """Number of unordered vertex pairs not within distance D (0 means diameter <= D)."""
    n2 = 2 * N
    adj = [[] for _ in range(n2)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    reach = [1 << v for v in range(n2)]
    for _ in range(D):
        new = []
        for v in range(n2):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    bad = sum(n2 - r.bit_count() for r in reach)
    return bad // 2


def _anneal(N, d, D, rng, deadline):
    """Anneal edge switches until cost 0 or the deadline. Returns edge list or None."""
    E = _random_bireg(N, d, rng)
    m = len(E)
    if m < 2:
        return None
    S = set(E)
    cur = _cost(N, D, E)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 1.5, 0.05
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        new = _cost(N, D, E)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S.discard((a1, b1))
            S.discard((a2, b2))
            S.add((a1, b2))
            S.add((a2, b1))
            cur = new
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return E


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = _kdd(d)
    if D == 2:
        return best

    pg = _pg_if_optimal(d, D)
    if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
        return pg

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Per-side size N gives order 2N; start just above the current best.
    N = max(d, best[0] // 2 + 1)
    while time.monotonic() < deadline and 2 * N <= moore:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        slice_end = min(deadline, time.monotonic() + max(3.0, 0.4 * remaining))
        E = _anneal(N, d, D, rng, slice_end)
        if E is None:
            # One more try at this size with all remaining time, otherwise stop.
            remaining = deadline - time.monotonic()
            if remaining > 5.0:
                E = _anneal(N, d, D, rng, deadline)
            if E is None:
                break
        edges = [(a, N + b) for a, b in E]
        consider(2 * N, edges)
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = _kdd(d)
    return best
