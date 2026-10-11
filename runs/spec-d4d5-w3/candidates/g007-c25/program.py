import math
import random
import time

import lib


FRAC_TOTAL = 0.85


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (bitmask BFS of radius D)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _adj(h, E):
    """Adjacency lists for the bipartite graph with A = 0..h-1 and B = h..2h-1; E holds (a, b) local pairs."""
    adj = [[] for _ in range(2 * h)]
    for a, b in E:
        adj[a].append(h + b)
        adj[h + b].append(a)
    return adj


def _anneal(h, D, E, deadline, rng):
    """Degree-preserving double-edge-swap annealing on the bipartite graph.

    Minimises the number of pairs at distance > D. Returns the edge list
    once the cost reaches zero, or None if the deadline passes first.
    """
    n = 2 * h
    E = list(E)
    m = len(E)
    exist = set(E)
    cost = _bad_pairs(n, _adj(h, E), D)
    if cost == 0:
        return E
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while True:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = 1.5 * (0.02 ** ((now - t0) / span))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        f1 = (a, e)
        f2 = (c, b)
        if f1 in exist or f2 in exist:
            continue
        E[i] = f1
        E[j] = f2
        new = _bad_pairs(n, _adj(h, E), D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            exist.discard((a, b))
            exist.discard((c, e))
            exist.add(f1)
            exist.add(f2)
            cost = new
            if cost == 0:
                return E
        else:
            E[i] = (a, b)
            E[j] = (c, e)


def _grow(h, d, E, rng):
    """Add one vertex on each side of a d-regular bipartite graph.

    Remove d edges with distinct A-ends and distinct B-ends, attach the new
    A vertex to the d freed B-ends and the new B vertex to the d freed A-ends.
    Degrees stay exactly d; the result is a d-regular bipartite graph on h+1 per side.
    """
    if len(E) < d:
        return None
    idx = None
    for _ in range(300):
        cand = rng.sample(range(len(E)), d)
        xs = {E[k][0] for k in cand}
        ys = {E[k][1] for k in cand}
        if len(xs) == d and len(ys) == d:
            idx = cand
            break
    if idx is None:
        return None
    drop = set(idx)
    newE = [E[k] for k in range(len(E)) if k not in drop]
    for y in ys:
        newE.append((h, y))
    for x in xs:
        newE.append((x, h))
    return h + 1, newE


def _search(d, D, start, deadline, rng, best, moore):
    """Grow a d-regular bipartite graph one vertex per side at a time, annealing after each growth step."""
    h = d
    E = [(a, b) for a in range(d) for b in range(d)]
    total = max(1e-3, deadline - start)
    while time.monotonic() < deadline:
        if 2 * (h + 1) > moore:
            break
        g = _grow(h, d, E, rng)
        if g is None:
            break
        h2, E2 = g
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0:
            break
        budget = min(remaining, max(1.0, 0.1 * total))
        res = _anneal(h2, D, E2, now + budget, rng)
        if res is not None:
            h, E = h2, res
            cand_edges = [(a, h + b) for a, b in E]
            cand = (2 * h, cand_edges)
            if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                best = cand
        # On failure, keep the last valid state and retry growth with new randomness.
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + FRAC_TOTAL * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D  # even cycle: bipartite, diameter D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # K_{d,d} has diameter 2 and is the always-valid fallback.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback
    moore = lib.moore_bound(d, D)

    # Projective plane incidence graph as an alternative base for D >= 3.
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                break
        if best[0] >= moore:
            return best

    # Main search: degree-preserving annealing with incremental vertex growth.
    try:
        best = _search(d, D, start, deadline, rng, best, moore)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
