import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction for D >= 4 (and the general fallback for D = 3):
# a d-regular bipartite graph on N + N vertices, found by simulated annealing
# over double-edge swaps. The cost is the number of vertex pairs at distance
# greater than D. The order is grown by inserting vertex pairs into a valid
# graph and re-annealing, so every accepted state is a valid graph.
# ----------------------------------------------------------------------------

ANNEAL_ITERS = 1500   # swap proposals per annealing attempt
_KEY_SHIFT = 20       # edge key = (a << 20) | b, with b < 2**20


def _key(a, b):
    return (a << _KEY_SHIFT) | b


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _cost(N, D, EA, EB):
    """Number of unordered vertex pairs at distance > D in the bipartite graph.

    A-vertices are 0..N-1 and B-vertices are N..2N-1; edge i joins A-vertex EA[i]
    to B-vertex N + EB[i].
    """
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in zip(EA, EB):
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
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _haar_state(N, d, rng):
    """Start from a Haar-style d-regular bipartite graph with d distinct shifts (needs N >= d)."""
    shifts = rng.sample(range(N), d)
    EA, EB = [], []
    for a in range(N):
        for s in shifts:
            EA.append(a)
            EB.append((a + s) % N)
    keys = {_key(a, b) for a, b in zip(EA, EB)}
    return EA, EB, keys


def _anneal(N, D, EA, EB, keys, cost, rng, iters, deadline):
    """Simulated annealing with double-edge swaps (keeps the graph d-regular and simple)."""
    M = len(EA)
    T0 = 1.0 + 0.02 * cost
    T1 = 0.15
    ratio = (T1 / T0) ** (1.0 / max(1, iters))
    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T *= ratio
        i = random.randrange(M)
        j = random.randrange(M)
        if i == j:
            continue
        a1, b1, a2, b2 = EA[i], EB[i], EA[j], EB[j]
        if a1 == a2 or b1 == b2:
            continue
        k1 = _key(a1, b2)
        k2 = _key(a2, b1)
        if k1 in keys or k2 in keys:
            continue
        keys.discard(_key(a1, b1))
        keys.discard(_key(a2, b2))
        keys.add(k1)
        keys.add(k2)
        EB[i] = b2
        EB[j] = b1
        c2 = _cost(N, D, EA, EB)
        delta = c2 - cost
        if delta <= 0 or random.random() < math.exp(-delta / T):
            cost = c2
        else:
            EB[i] = b1
            EB[j] = b2
            keys.discard(k1)
            keys.discard(k2)
            keys.add(_key(a1, b1))
            keys.add(_key(a2, b2))
    return cost


def _insert_pair(N, d, EA, EB, keys, rng):
    """Add one new A-vertex (index N) and one new B-vertex (index N), keeping d-regularity.

    Pick d edges (x_i, y_i) with pairwise distinct x_i and distinct y_i. Replace each by
    (x_i, newB) and add (newA, y_i). Every old vertex keeps its degree; the new vertices
    have degree d. Returns False if no such d edges exist.
    """
    order = list(range(len(EA)))
    rng.shuffle(order)
    used_a, used_b, chosen = set(), set(), []
    for i in order:
        a, b = EA[i], EB[i]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append(i)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return False
    newA = N
    newB = N
    for i in chosen:
        x, y = EA[i], EB[i]
        keys.discard(_key(x, y))
        EB[i] = newB
        keys.add(_key(x, newB))
        EA.append(newA)
        EB.append(y)
        keys.add(_key(newA, y))
    return True


def _to_edges(N, EA, EB):
    return 2 * N, [(a, N + b) for a, b in zip(EA, EB)]


def _grow_search(d, D, moore, rng, deadline):
    """Anneal a d-regular bipartite graph, then repeatedly grow it and re-anneal.

    Returns the largest valid (n, edges) found, or None if the start never reaches cost 0.
    """
    N = max(d, min(moore // 8, 200))
    EA, EB, keys = _haar_state(N, d, rng)
    cost = _anneal(N, D, EA, EB, keys, _cost(N, D, EA, EB), rng,
                   4 * ANNEAL_ITERS, deadline)
    if cost != 0:
        return None
    best = _to_edges(N, EA, EB)
    step = 8
    while time.monotonic() < deadline:
        room = moore // 2 - N
        if room < 1:
            break
        s = min(step, room)
        sA, sB, sK, sN = EA[:], EB[:], set(keys), N
        ok = True
        for _ in range(s):
            if not _insert_pair(N, d, EA, EB, keys, rng):
                ok = False
                break
            N += 1
        cost = None
        if ok:
            cost = _anneal(N, D, EA, EB, keys, _cost(N, D, EA, EB), rng,
                           ANNEAL_ITERS, deadline)
        if ok and cost == 0:
            best = _to_edges(N, EA, EB)
            step = min(16, step * 2)
        else:
            EA, EB, keys = sA, sB, sK
            N = sN
            step = max(1, step // 2)
    return best


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)
    random.seed(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D  # even cycle of length 2D has diameter D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # Safe fallback: K_{d,d} has diameter 2 and meets the Moore bound for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
        if best[0] >= moore:
            return best

    try:
        cand = _grow_search(d, D, moore, rng, deadline)
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
