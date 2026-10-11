import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base (diameter 3), used for the calibration case.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: edge-switch annealing on bipartite graphs with insertion growth.
#
# A bipartite graph with sides L = {0..m-1} and R = {0..m-1} is stored as a list E
# of pairs (a, b). Vertex a in L is graph vertex a, vertex b in R is graph vertex m+b.
#
# Move: pick two edges (a,b), (c,e) and replace them with (a,e), (c,b). Every degree
# and the bipartition are preserved. The cost is the number of vertex pairs at
# distance greater than D, computed with bitmask balls. Simulated annealing drives
# the cost to zero.
#
# Growth: from a valid m-side graph, add one vertex to each side. Each new vertex
# receives d edges by splitting random old edges (a,b) into (a,new_R) and (new_L,b).
# Old degrees are unchanged. The result is then annealed back to diameter <= D.
# ----------------------------------------------------------------------------

def _cost(N, adj, D):
    """Unordered pairs at distance > D, computed from bitmask balls."""
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        nb = []
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb.append(x)
        ball = nb
    return sum(N - b.bit_count() for b in ball) // 2


def _mod(adj, m, rem, add):
    """Remove the edges in rem and add the edges in add, updating adjacency lists in place."""
    for a, b in rem:
        adj[a].remove(m + b)
        adj[m + b].remove(a)
    for a, b in add:
        adj[a].append(m + b)
        adj[m + b].append(a)


def _random_regular(m, d, rng):
    """Union of d random permutations between the two sides (duplicates removed)."""
    S = set()
    for _ in range(d):
        p = list(range(m))
        rng.shuffle(p)
        for a in range(m):
            S.add((a, p[a]))
    return list(S)


def _insert_pair(m, E, d, rng):
    """Add one new left and one new right vertex, each of degree up to d, by splitting old edges."""
    pool = list(E)
    newE = []
    for _ in range(d):
        if not pool:
            break
        k = rng.randrange(len(pool))
        a, b = pool[k]
        pool[k] = pool[-1]
        pool.pop()
        newE.append((a, m))
        newE.append((m, b))
    return pool + newE


def _anneal(m, D, E, rng, deadline, iters):
    """Edge-switch simulated annealing. Returns the edge list if diameter <= D is reached, else None."""
    E = list(E)
    Eset = set(E)
    N = 2 * m
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(m + b)
        adj[m + b].append(a)
    cost = _cost(N, adj, D)
    T0, T1 = 2.0, 0.1
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline or len(E) < 2:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or (a, e) in Eset or (c, b) in Eset:
            continue
        rem = [(a, b), (c, e)]
        add = [(a, e), (c, b)]
        _mod(adj, m, rem, add)
        c2 = _cost(N, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            E[i] = (a, e)
            E[j] = (c, b)
            Eset.discard((a, b))
            Eset.discard((c, e))
            Eset.add((a, e))
            Eset.add((c, b))
        else:
            _mod(adj, m, add, rem)
    return E if cost == 0 else None


def _to_graph(m, E):
    """Convert a bipartite (m, E) description to (n, edges) with left a and right m+b."""
    return 2 * m, [(a, m + b) for a, b in E]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
            return pg

    best_n = best[0]

    def consider(n, edges):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            best_n = n

    # Switch-annealing growth. Start from a random regular bipartite graph, anneal to
    # diameter <= D, then repeatedly grow by one vertex per side and re-anneal.
    cur_m, cur_E = None, None
    m0 = d + 1
    while cur_E is None and time.monotonic() < deadline:
        E0 = _random_regular(m0, d, rng)
        res = _anneal(m0, D, E0, rng, deadline, iters=4000)
        if res is not None:
            cur_m, cur_E = m0, res

    if cur_E is not None:
        consider(*_to_graph(cur_m, cur_E))

    ITERS = 2500
    while cur_E is not None and time.monotonic() < deadline:
        new_m = cur_m + 1
        E1 = _insert_pair(cur_m, cur_E, d, rng)
        res = _anneal(new_m, D, E1, rng, deadline, iters=ITERS)
        if res is not None:
            cur_m, cur_E = new_m, res
            consider(*_to_graph(cur_m, cur_E))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
