import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New approach: simulated annealing over bipartite d-regular graphs with edge
# switches, growing one vertex per side at a time. Diameter is measured with
# big-int bitsets of ball contents, and the cost is the number of ordered
# vertex pairs at distance > D. A zero-cost level is a valid graph.
# ----------------------------------------------------------------------------

CHUNK = 2000        # annealing moves per chunk (each chunk reheats the schedule)
MAX_CHUNKS = 4      # chunks allowed before giving up on a level with no success yet
T_START = 1.5
T_END = 0.1


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost(N, adj, D):
    """Number of ordered vertex pairs at distance more than D (zero iff diameter <= D)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _swap(adj, E, eset, i, j):
    """Edge switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Applying it twice on (i, j) reverts it."""
    a1, b1 = E[i]
    a2, b2 = E[j]
    eset.discard((a1, b1))
    eset.discard((a2, b2))
    eset.add((a1, b2))
    eset.add((a2, b1))
    adj[a1][adj[a1].index(b1)] = b2
    adj[b1][adj[b1].index(a1)] = a2
    adj[a2][adj[a2].index(b2)] = b1
    adj[b2][adj[b2].index(a2)] = a1
    E[i] = (a1, b2)
    E[j] = (a2, b1)


def _adj_of(n, E):
    """Global adjacency lists (A ids 0..n-1, B ids n..2n-1) and the edge set."""
    adj = [[] for _ in range(2 * n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    return adj, set(E)


def _random_regular(n, d, rng):
    """Random d-regular bipartite graph with n vertices per side, or None if it fails."""
    if n < 1:
        return None
    E = []
    eset = set()
    for _ in range(d):
        ok = False
        for _attempt in range(500):
            p = list(range(n))
            rng.shuffle(p)
            if all((i, n + p[i]) not in eset for i in range(n)):
                ok = True
                break
        if not ok:
            return None
        for i in range(n):
            e = (i, n + p[i])
            eset.add(e)
            E.append(e)
    return E


def _anneal(n, E, eset, adj, D, rng, iters, deadline):
    """Metropolis annealing on edge switches; returns the final cost (0 means valid)."""
    N = 2 * n
    m = len(E)
    cost = _cost(N, adj, D)
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or (a1, b2) in eset or (a2, b1) in eset:
            continue
        T = T_START * (T_END / T_START) ** (it / max(1, iters))
        _swap(adj, E, eset, i, j)
        c2 = _cost(N, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _swap(adj, E, eset, i, j)
    return cost


def _grow(n, E, d, rng):
    """Add one vertex per side. Remove d edges with distinct endpoints and reattach them
    to the two new vertices, which keeps the graph d-regular. Returns (n+1, E) or None."""
    idxs = list(range(len(E)))
    rng.shuffle(idxs)
    usedA, usedB, rem = set(), set(), set()
    for i in idxs:
        a, b = E[i]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        rem.add(i)
        if len(rem) == d:
            break
    if len(rem) < d:
        return None

    def remap(x):
        return x if x < n else x + 1

    newA = n
    newB = 2 * n + 1
    newE = []
    for i, (a, b) in enumerate(E):
        if i in rem:
            continue
        newE.append((a, remap(b)))
    for b in usedB:
        newE.append((newA, remap(b)))
    for a in usedA:
        newE.append((a, newB))
    return n + 1, newE


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (and is valid for D >= 2).
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if best[0] >= moore:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if best[0] >= moore:
            return best

    # Annealing growth from a small random regular bipartite graph.
    moore_side = moore // 2
    best_side = best[0] // 2
    n = max(d, min(best_side + 1, int(0.4 * moore_side)))

    E = None
    while E is None and n >= 1 and time.monotonic() < deadline:
        E = _random_regular(n, d, rng)
        if E is None:
            n -= 1

    succeeded = False
    while E is not None and time.monotonic() < deadline:
        adj, eset = _adj_of(n, E)
        solved = False
        chunks = 0
        cost = 1
        while time.monotonic() < deadline:
            cost = _anneal(n, E, eset, adj, D, rng, CHUNK, deadline)
            chunks += 1
            if cost == 0:
                solved = True
                break
            if not succeeded and chunks >= MAX_CHUNKS:
                break

        if solved:
            consider(2 * n, list(E))
            succeeded = True
            grown = _grow(n, E, d, rng)
            if grown is None:
                break
            n, E = grown
        else:
            if succeeded:
                break
            # Level too hard from scratch: back off and restart with a fresh graph.
            n = max(d, int(n * 0.92))
            if n <= d and n == d and time.monotonic() >= deadline:
                break
            E = _random_regular(n, d, rng)
            if E is None:
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
