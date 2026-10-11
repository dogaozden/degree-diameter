import math
import random
import time

import lib


ANNEAL_ITERS = 400   # annealing moves per attempt at a fixed side size N


def _balls_bits(n, adj, D):
    """Bitmask per vertex of all vertices within distance D."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        if new == ball:
            break
        ball = new
    return ball


def _cost(N, E, D):
    """Number of unordered vertex pairs at distance > D in the bipartite graph
    with left vertices 0..N-1, right vertices N..2N-1, and edges (x, y) meaning x ~ N+y."""
    n = 2 * N
    adj = [[] for _ in range(n)]
    for x, y in E:
        adj[x].append(N + y)
        adj[N + y].append(x)
    ball = _balls_bits(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _anneal(N, E, D, rng, deadline, iters):
    """Simulated annealing over 2-switches (keeps degrees and bipartiteness).
    Modifies E in place. Returns the final cost (0 means diameter <= D)."""
    cost = _cost(N, E, D)
    if cost == 0:
        return 0
    Eset = set(E)
    T0 = 2.0
    for it in range(iters):
        if time.monotonic() > deadline or len(E) < 2:
            break
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        x1, y1 = E[i]
        x2, y2 = E[j]
        if x1 == x2 or y1 == y2:
            continue
        if (x1, y2) in Eset or (x2, y1) in Eset:
            continue
        T = T0 * (1.0 - it / iters) + 0.05
        E[i] = (x1, y2)
        E[j] = (x2, y1)
        Eset.discard((x1, y1))
        Eset.discard((x2, y2))
        Eset.add((x1, y2))
        Eset.add((x2, y1))
        c2 = _cost(N, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                return 0
        else:
            E[i] = (x1, y1)
            E[j] = (x2, y2)
            Eset.discard((x1, y2))
            Eset.discard((x2, y1))
            Eset.add((x1, y1))
            Eset.add((x2, y2))
    return cost


def _grow(N, E, d, rng):
    """Add one left and one right vertex, keeping d-regularity: subdivide d edges
    with pairwise distinct endpoints. Returns the new side size, or None on failure."""
    order = list(range(len(E)))
    rng.shuffle(order)
    usedx, usedy, chosen = set(), set(), []
    for idx in order:
        x, y = E[idx]
        if x in usedx or y in usedy:
            continue
        usedx.add(x)
        usedy.add(y)
        chosen.append(idx)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    cs = set(chosen)
    newE = [e for k, e in enumerate(E) if k not in cs]
    a = N  # new left vertex
    b = N  # new right vertex
    for idx in chosen:
        x, y = E[idx]
        newE.append((x, b))
        newE.append((a, y))
    E[:] = newE
    return N + 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    rng = random.Random(seed)

    # Structured candidate for D = 3: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n2, e2 = lib.projective_plane_incidence(d - 1)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)

    # Main search: grow a d-regular bipartite graph one vertex per side at a time,
    # re-annealing 2-switches to restore diameter <= D after each growth step.
    N = d
    E = [(x, y) for x in range(N) for y in range(N)]
    while time.monotonic() < deadline:
        ok = _anneal(N, E, D, rng, deadline, ANNEAL_ITERS) == 0
        if not ok:
            continue
        if 2 * N > best[0]:
            edges = [(x, N + y) for x, y in E]
            if lib.is_valid(2 * N, edges, d, D):
                best = (2 * N, edges)
        nxt = _grow(N, E, d, rng)
        if nxt is None:
            break
        N = nxt

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
