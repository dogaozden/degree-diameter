import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction: grow-and-repair on bipartite d-regular graphs.
#
# Instead of searching bi-Cayley or voltage lifts, this keeps a d-regular
# bipartite graph and repeats two steps:
#   1. Anneal with degree-preserving edge swaps until the number of ordered
#      pairs at distance > D is zero (a valid graph).
#   2. Grow by two vertices: a new A-vertex and a new B-vertex take over d
#      disjoint edges (x_i, y_i). Each edge becomes x_i-b' and a'-y_i, so all
#      degrees stay exactly d. Then go back to step 1.
#
# Every graph returned is checked with lib.is_valid. If anything fails, the
# output falls back to the safe K_{d,d} (or the projective plane for D = 3).
# ----------------------------------------------------------------------------

_ITERS_PER_TEMP = 3000


def _pg_baseline(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bad_pairs(n, adj, D):
    """Ordered count of vertex pairs at distance > D, via bitset BFS."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _adj(N, ea, eb):
    """Full adjacency: A-vertices 0..N-1, B-vertices N..2N-1."""
    adj = [[N + b for b in row] for row in ea]
    adj.extend(list(row) for row in eb)
    return adj


def _seed(N, d, rng):
    """Haar graph of Z_N with d random shifts, stored as ea (A -> B) and eb (B -> A)."""
    S = rng.sample(range(N), d)
    ea = [[(i + s) % N for s in S] for i in range(N)]
    eb = [[] for _ in range(N)]
    for i in range(N):
        for b in ea[i]:
            eb[b].append(i)
    return ea, eb


def _anneal(N, d, D, ea, eb, rng, deadline):
    """Degree-preserving edge-swap annealing. Returns True iff the graph becomes valid."""
    n = 2 * N
    cost = _bad_pairs(n, _adj(N, ea, eb), D)
    it = 0
    while cost > 0:
        it += 1
        if (it & 7) == 0 and time.monotonic() > deadline:
            return False
        temp = 0.3 + 1.2 * (1.0 - (it % _ITERS_PER_TEMP) / _ITERS_PER_TEMP)

        a1 = rng.randrange(N)
        a2 = rng.randrange(N)
        if a1 == a2:
            continue
        i = rng.randrange(d)
        j = rng.randrange(d)
        b1 = ea[a1][i]
        b2 = ea[a2][j]
        if b1 == b2 or b2 in ea[a1] or b1 in ea[a2]:
            continue

        # Save the four affected rows for undo.
        s1, s2 = ea[a1][:], ea[a2][:]
        t1, t2 = eb[b1][:], eb[b2][:]

        # Swap (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
        ea[a1][i] = b2
        ea[a2][j] = b1
        eb[b1][eb[b1].index(a1)] = a2
        eb[b2][eb[b2].index(a2)] = a1

        c2 = _bad_pairs(n, _adj(N, ea, eb), D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = c2
        else:
            ea[a1] = s1
            ea[a2] = s2
            eb[b1] = t1
            eb[b2] = t2
    return True


def _grow(N, d, ea, eb, rng):
    """Add one A-vertex and one B-vertex, keeping the graph d-regular. Returns False on failure."""
    edges = [(x, y) for x in range(N) for y in ea[x]]
    rng.shuffle(edges)
    usedx, usedy, chosen = set(), set(), []
    for x, y in edges:
        if x in usedx or y in usedy:
            continue
        usedx.add(x)
        usedy.add(y)
        chosen.append((x, y))
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return False
    ea.append([])  # new A index N
    eb.append([])  # new B index N
    na, nb = N, N
    for x, y in chosen:
        # Remove (x, y); add (x, nb) and (na, y).
        ea[x][ea[x].index(y)] = nb
        eb[y][eb[y].index(x)] = na
        eb[nb].append(x)
        ea[na].append(y)
    return True


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and meets the Moore bound for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d == 1:
        return best

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _pg_baseline(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if best[0] >= moore:
            return best

    # Grow-and-repair search.
    N0 = max(d, min(moore // 2, 24))
    if N0 > moore // 2:
        return best
    ea, eb = _seed(N0, d, rng)
    N = N0
    while time.monotonic() < deadline:
        if not _anneal(N, d, D, ea, eb, rng, deadline):
            break
        n = 2 * N
        if n > best[0]:
            edges = [(a, N + b) for a in range(N) for b in ea[a]]
            consider(n, edges)
        if 2 * (N + 1) > moore:
            break
        if not _grow(N, d, ea, eb, rng):
            break
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
