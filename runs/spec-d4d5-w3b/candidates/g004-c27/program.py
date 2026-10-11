import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Unstructured search: bipartite edge-switch annealing with edge-splitting growth.
#
# A d-regular bipartite graph with sides A = {0..m-1} and B = {0..m-1} is kept
# as two adjacency-list arrays. Moves are degree-preserving edge switches:
# (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Cost = number of unordered vertex pairs
# at distance > D, computed exactly with big-int bitset balls. When cost hits
# zero, the graph is grown by splitting d edges: each split edge (a,b) becomes
# (a,newB),(newA,b), so degrees stay d and both sides gain one vertex.
# ----------------------------------------------------------------------------


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _unified(mA, adjA, adjB):
    """Single adjacency list: A vertex a -> a, B vertex b -> mA + b."""
    adj = [None] * (2 * mA)
    for a in range(mA):
        adj[a] = [mA + b for b in adjA[a]]
    for b in range(mA):
        adj[mA + b] = adjB[b]
    return adj


def _bad(adj, N, D):
    """Number of unordered vertex pairs at distance greater than D."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


def _move_edge(adjA, adjB, a, k, newb):
    """Re-point the k-th A-edge of a from its current B-neighbour to newb."""
    old = adjA[a][k]
    adjA[a][k] = newb
    adjB[old].remove(a)
    adjB[newb].append(a)


def _circulant(m, d, rng):
    """Random Haar-type start: A_i ~ B_{i+s} for s in a random d-subset of Z_m."""
    S = rng.sample(range(m), d)
    adjA = [[(i + s) % m for s in S] for i in range(m)]
    adjB = [[(j - s) % m for s in S] for j in range(m)]
    return adjA, adjB


def _copy(adjA, adjB):
    return [list(x) for x in adjA], [list(x) for x in adjB]


def _grow(adjA, adjB, mA, d, rng):
    """Add one A vertex and one B vertex by splitting d edges; True on success."""
    pairs = None
    for _ in range(60):
        As = rng.sample(range(mA), d)
        cand = []
        bs = set()
        ok = True
        for a in As:
            b = rng.choice(adjA[a])
            if b in bs:
                ok = False
                break
            bs.add(b)
            cand.append((a, b))
        if ok:
            pairs = cand
            break
    if pairs is None:
        return False
    newA = mA
    newB = mA
    adjA.append([])
    adjB.append([])
    for a, b in pairs:
        k = adjA[a].index(b)
        adjA[a][k] = newB
        adjB[b][adjB[b].index(a)] = newA
        adjA[newA].append(b)
        adjB[newB].append(a)
    return True


def _anneal(adjA, adjB, mA, d, D, rng, deadline, iters):
    """Edge-switch annealing; True if the graph reaches zero bad pairs."""
    N = 2 * mA
    cur = _bad(_unified(mA, adjA, adjB), N, D)
    T = 0.6
    for it in range(iters):
        if cur == 0:
            return True
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        a1 = rng.randrange(mA)
        a2 = rng.randrange(mA)
        if a1 == a2:
            continue
        k1 = rng.randrange(len(adjA[a1]))
        k2 = rng.randrange(len(adjA[a2]))
        b1 = adjA[a1][k1]
        b2 = adjA[a2][k2]
        if b1 == b2 or b2 in adjA[a1] or b1 in adjA[a2]:
            continue
        _move_edge(adjA, adjB, a1, k1, b2)
        _move_edge(adjA, adjB, a2, k2, b1)
        c2 = _bad(_unified(mA, adjA, adjB), N, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
            cur = c2
        else:
            _move_edge(adjA, adjB, a2, k2, b2)
            _move_edge(adjA, adjB, a1, k1, b1)
    return cur == 0


def _to_edges(mA, adjA):
    return 2 * mA, [(a, mA + b) for a in range(mA) for b in adjA[a]]


def _run(d, D, seed, deadline, state):
    """Grow zero-cost graphs by edge-splitting; anneal after each growth step."""
    rng = random.Random(seed)
    moore = lib.moore_bound(d, D)
    m0 = max(d, state['best'][0] // 2 - 2)
    saved = None  # (mS, adjA copy, adjB copy) of the last zero-cost graph
    fails = 0
    while time.monotonic() < deadline:
        if saved is None:
            mA = m0
            adjA, adjB = _circulant(mA, d, rng)
        else:
            mS, sA, sB = saved
            adjA, adjB = _copy(sA, sB)
            if not _grow(adjA, adjB, mS, d, rng):
                fails += 1
                continue
            mA = mS + 1
        if _anneal(adjA, adjB, mA, d, D, rng, deadline, 4000):
            fails = 0
            n, edges = _to_edges(mA, adjA)
            if n > state['best'][0] and lib.is_valid(n, edges, d, D):
                state['best'] = (n, edges)
            if 2 * mA >= moore:
                return
            saved = (mA, *_copy(adjA, adjB))
        else:
            fails += 1
            if saved is None and fails >= 3:
                m0 = max(d, m0 - 1)
                fails = 0


def build(d, D, seed, time_limit):
    start = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    state = {'best': fallback}
    moore = lib.moore_bound(d, D)

    try:
        if D >= 3 and state['best'][0] < moore:
            pg = _pg_candidate(d)
            if pg is not None and pg[0] > state['best'][0] and lib.is_valid(pg[0], pg[1], d, D):
                state['best'] = pg
        if state['best'][0] < moore:
            _run(d, D, seed, start + 0.80 * time_limit, state)
    except Exception:
        pass  # keep the best valid graph found so far

    best = state['best']
    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
