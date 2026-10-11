import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines (instant, always valid).
# ----------------------------------------------------------------------------

def _haar_fallback(d):
    """K_{d,d}: diameter 2, degree d. Valid for every D >= 2."""
    return lib.haar_graph(d, range(d))


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: degree-preserving switch annealing on bipartite d-regular graphs.
#
# No algebraic structure is imposed. The state is a d-regular bipartite graph
# on n + n vertices (A = 0..n-1, B = n..2n-1). Moves are edge switches
# (a,b),(c,e) -> (a,e),(c,b), which keep every degree equal to d. The cost is
# the number of unordered pairs at distance > D, computed with big-int
# bitsets. Once a zero-cost graph is found, it grows by one A and one B vertex:
# d disjoint edges (a_i,b_i) are replaced by x-b_i and a_i-y, where x and y are
# the new vertices. This keeps the graph d-regular, and annealing resumes from
# the grown state.
# ----------------------------------------------------------------------------

def _adj_list(n, adjA, adjB):
    adj = [None] * (2 * n)
    for a in range(n):
        adj[a] = [n + b for b in adjA[a]]
    for b in range(n):
        adj[n + b] = list(adjB[b])
    return adj


def _bad(n, adjA, adjB, D):
    """Number of unordered vertex pairs at distance > D."""
    N = 2 * n
    adj = _adj_list(n, adjA, adjB)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _propose(E, adjA, rng):
    """Random switch candidate (i, j) or None if it is not legal."""
    m = len(E)
    i = rng.randrange(m)
    j = rng.randrange(m)
    if i == j:
        return None
    a, b = E[i]
    c, e = E[j]
    if a == c or b == e or e in adjA[a] or b in adjA[c]:
        return None
    return i, j


def _replace(adjA, adjB, E, i, j, p, q):
    """Replace edges E[i] and E[j] by p and q, updating adjacency and E."""
    a, b = E[i]
    c, e = E[j]
    adjA[a].discard(b)
    adjB[b].discard(a)
    adjA[c].discard(e)
    adjB[e].discard(c)
    for x, y in (p, q):
        adjA[x].add(y)
        adjB[y].add(x)
    E[i] = p
    E[j] = q


def _anneal(n, D, adjA, adjB, E, rng, deadline, iters):
    """Simulated annealing over degree-preserving switches. Returns the final cost."""
    cost = _bad(n, adjA, adjB, D)
    T0, T1 = 1.0, 0.05
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        pr = _propose(E, adjA, rng)
        if pr is None:
            continue
        i, j = pr
        a, b = E[i]
        c, e = E[j]
        old_i, old_j = E[i], E[j]
        _replace(adjA, adjB, E, i, j, (a, e), (c, b))
        c2 = _bad(n, adjA, adjB, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _replace(adjA, adjB, E, i, j, old_i, old_j)
    return cost


def _insert(n, adjA, adjB, E, d, rng):
    """Grow a d-regular bipartite graph by one A and one B vertex. Returns the new state or None."""
    order = list(range(len(E)))
    rng.shuffle(order)
    usedA, usedB, chosen = set(), set(), []
    for idx in order:
        a, b = E[idx]
        if a in usedA or b in usedB:
            continue
        chosen.append((a, b))
        usedA.add(a)
        usedB.add(b)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    x = n          # new A vertex
    y = n          # new B vertex
    adjA.append(set())
    adjB.append(set())
    for a, b in chosen:
        adjA[a].discard(b)
        adjB[b].discard(a)
        adjA[a].add(y)
        adjB[y].add(a)
        adjA[x].add(b)
        adjB[b].add(x)
    E2 = [(a, b) for a in range(n + 1) for b in adjA[a]]
    return n + 1, adjA, adjB, E2


def _search(d, D, deadline, rng, n0):
    """Grow d-regular bipartite graphs with diameter <= D. Returns the largest (N, edges) found."""
    n = n0
    adjA = [set() for _ in range(n)]
    adjB = [set() for _ in range(n)]
    shifts = rng.sample(range(n), d)
    for a in range(n):
        for s in shifts:
            b = (a + s) % n
            adjA[a].add(b)
            adjB[b].add(a)
    E = [(a, b) for a in range(n) for b in adjA[a]]

    last = None
    while time.monotonic() < deadline:
        cost = _anneal(n, D, adjA, adjB, E, rng, deadline, 4000)
        if cost == 0:
            edges = [(a, n + b) for a in range(n) for b in adjA[a]]
            last = (2 * n, edges)
            res = _insert(n, adjA, adjB, E, d, rng)
            if res is None:
                break
            n, adjA, adjB, E = res
    return last


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)
    best = _haar_fallback(d)

    def consider(N, E):
        nonlocal best
        if N > best[0] and lib.is_valid(N, E, d, D):
            best = (N, E)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    elif D >= 4 and d >= 2:
        sol = _search(d, D, deadline, rng, max(d, 2))
        if sol is not None:
            consider(sol[0], sol[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = _haar_fallback(d)
    return best[0], list(best[1])
