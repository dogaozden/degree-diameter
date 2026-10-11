import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold family: simulated annealing over bipartite d-regular graphs with
# double-edge swaps, minimising the number of vertex pairs at distance > D.
# Vertices: A-side 0..N-1, B-side 0..N-1 (B index j is output as N + j).
# Growth: insert one new A and one new B vertex by splitting d disjoint edges,
# then re-anneal. Every accepted state is a simple, d-regular bipartite graph.
# ----------------------------------------------------------------------------

FIRST_ITERS = 20000
GROW_ITERS = 8000


def _cost(N, E, D):
    """Number of unordered vertex pairs at distance > D (0 means valid diameter)."""
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
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
    return sum(n - r.bit_count() for r in reach) // 2


def _random_start(N, d, rng):
    """Random simple d-regular bipartite edge list on N+N vertices (configuration model)."""
    for _ in range(300):
        A = [i for i in range(N) for _ in range(d)]
        B = A[:]
        rng.shuffle(B)
        pairs = list(zip(A, B))
        if len(set(pairs)) == len(pairs):
            return pairs
    # Deterministic fallback: circulant, simple since d <= N.
    return [(i, (i + s) % N) for i in range(N) for s in range(d)]


def _anneal(N, E, S, D, rng, deadline, iters, T0, T1):
    """Double-edge-swap annealing. E is a list of (a, b) tuples, S the same set."""
    cost = _cost(N, E, D)
    m = len(E)
    if m < 2:
        return cost
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in S or n2 in S:
            continue
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add(n1)
        S.add(n2)
        E[i] = n1
        E[j] = n2
        c2 = _cost(N, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            S.discard(n1)
            S.discard(n2)
            S.add((a1, b1))
            S.add((a2, b2))
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return cost


def _grow(N, E, S, d, rng):
    """Add one A and one B vertex by splitting d disjoint edges; keeps d-regularity and simplicity."""
    m = len(E)
    if m < d:
        return None
    idx = None
    for _ in range(2000):
        cand = rng.sample(range(m), d)
        xs = {E[i][0] for i in cand}
        ys = {E[i][1] for i in cand}
        if len(xs) == d and len(ys) == d:
            idx = cand
            break
    if idx is None:
        return None
    idxset = set(idx)
    newE = [e for k, e in enumerate(E) if k not in idxset]
    newA = N
    newB = N
    for i in idx:
        x, y = E[i]
        S.discard((x, y))
        p = (newA, y)
        q = (x, newB)
        S.add(p)
        S.add(q)
        newE.append(p)
        newE.append(q)
    return N + 1, newE


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    budget = max(1.0, min(0.8 * time_limit, time_limit - 4.0))
    deadline = start + budget

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Starting size: a fraction of the per-side Moore bound, capped for speed.
    half = sum((d - 1) ** i for i in range(D))
    N = min(400, max(d + 1, int(0.6 * half)))

    E = None
    S = None
    cost = None
    while time.monotonic() < deadline:
        E = _random_start(N, d, rng)
        S = set(E)
        cost = _anneal(N, E, S, D, rng, deadline, FIRST_ITERS, 0.8, 0.2)
        if cost == 0:
            break
        if N <= d + 1:
            break
        N = max(d + 1, N - max(1, N // 20))

    if cost == 0:
        consider(2 * N, [(a, N + b) for a, b in E])
        # Grow one vertex per side at a time, re-annealing after each step.
        while time.monotonic() < deadline:
            g = _grow(N, E, S, d, rng)
            if g is None:
                break
            N, E = g
            cost = _anneal(N, E, S, D, rng, deadline, GROW_ITERS, 0.8, 0.2)
            if cost != 0:
                break
            consider(2 * N, [(a, N + b) for a, b in E])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
