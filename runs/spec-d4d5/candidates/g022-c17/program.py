import math
import random
import time

import lib


# Fraction of time_limit available to the search. The remainder covers
# validation and return overhead.
FRAC = 0.85
GQ_Q_MAX = 9


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bad_pairs(V, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable counts), via bitsets."""
    ball = [1 << v for v in range(V)]
    for _ in range(D):
        nb = []
        for v in range(V):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb.append(x)
        ball = nb
    return sum(V - x.bit_count() for x in ball) // 2


def _adjacency(V, E):
    adj = [[] for _ in range(V)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    return adj


def _search(d, D, N, rng, deadline):
    """Anneal a simple d-regular bipartite graph with N + N vertices and diameter <= D.

    Start from a random circulant (Haar graph over Z_N). Moves are degree-preserving
    edge switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). The cost is the number of
    vertex pairs at distance > D; zero means valid. Temperature cools with elapsed time.
    Returns the edge list (A = 0..N-1, B = N..2N-1) or None.
    """
    V = 2 * N
    shifts = rng.sample(range(N), d)
    E = [[i, N + (i + s) % N] for s in shifts for i in range(N)]
    Eset = {(a, b) for a, b in E}
    if len(Eset) != len(E):
        return None

    cost = _bad_pairs(V, _adjacency(V, E), D)
    if cost == 0:
        return [tuple(e) for e in E]

    T0, Tend = 2.0, 0.1
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    m = len(E)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (Tend / T0) ** min(1.0, (now - t0) / span)

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in Eset or (a2, b1) in Eset:
            continue

        Eset.discard((a1, b1))
        Eset.discard((a2, b2))
        Eset.add((a1, b2))
        Eset.add((a2, b1))
        E[i] = [a1, b2]
        E[j] = [a2, b1]

        c2 = _bad_pairs(V, _adjacency(V, E), D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            Eset.discard((a1, b2))
            Eset.discard((a2, b1))
            Eset.add((a1, b1))
            Eset.add((a2, b2))
            E[i] = [a1, b1]
            E[j] = [a2, b2]

    if cost == 0:
        return [tuple(e) for e in E]
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + FRAC * time_limit

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D  # even cycle: bipartite, diameter D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # K_{d,d} has diameter 2 and is the always-valid fallback.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    rng = random.Random(seed)
    nmax = moore // 2
    N = max(d, best[0] // 2 + 1)
    fails = 0

    try:
        while N <= nmax and time.monotonic() < deadline:
            remain = deadline - time.monotonic()
            budget = min(remain, max(3.0, 0.3 * remain))
            E = _search(d, D, N, rng, time.monotonic() + budget)
            if E is not None:
                n2 = 2 * N
                if n2 > best[0] and lib.is_valid(n2, E, d, D):
                    best = (n2, E)
                N += 1
                fails = 0
            else:
                fails += 1
                if fails >= 2:
                    break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
