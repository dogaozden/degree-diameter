import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Direct bipartite graph search (replaces the voltage-lift family).
#
# State: a bipartite graph with sides A = {0..h-1} and B = {0..h-1}, vertex
# ids A: a, B: h + b, max degree d. Adding edges never increases a distance,
# so the search only adds edges when both endpoints have spare degree and
# otherwise performs degree-preserving double-edge swaps. Cost = number of
# vertex pairs at distance > D (computed with bitsets).
#
# Growth: each step adds one vertex to each side by subdividing old edges
# (x-y becomes x-B_new and A_new-y), so old degrees are unchanged, and then
# joins A_new-B_new. The annealer repairs the diameter at the new size.
# The last valid graph is always kept; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------


def _cost(n, h, adjA, adjB, D):
    """Number of unordered vertex pairs at distance > D (0 means valid)."""
    nbr = [None] * n
    for a in range(h):
        nbr[a] = [b + h for b in adjA[a]]
    for b in range(h):
        nbr[h + b] = list(adjB[b])
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _fill(E, adjA, adjB):
    """Rebuild the adjacency sets in place from the edge list E."""
    for s in adjA:
        s.clear()
    for s in adjB:
        s.clear()
    for a, b in E:
        adjA[a].add(b)
        adjB[b].add(a)


def _extend(h, E, adjA, adjB, d, rng):
    """Add A-vertex h and B-vertex h, keeping every old degree unchanged."""
    adjA.append(set())
    adjB.append(set())
    done = 0
    tries = 0
    limit = 200 * d
    while done < d - 1 and tries < limit and E:
        tries += 1
        i = rng.randrange(len(E))
        x, y = E[i]
        if x == h or y == h:
            continue
        if y in adjA[h] or x in adjB[h]:
            continue
        # Replace x-y by h-y and append x-h.
        adjA[x].discard(y)
        adjB[y].discard(x)
        adjA[h].add(y)
        adjB[y].add(h)
        adjA[x].add(h)
        adjB[h].add(x)
        E[i] = (h, y)
        E.append((x, h))
        done += 1
    if len(adjA[h]) < d and len(adjB[h]) < d and h not in adjA[h]:
        adjA[h].add(h)
        adjB[h].add(h)
        E.append((h, h))


def _step(h, d, D, E, adjA, adjB, rng, cost, T):
    """One annealing move. Returns the new cost (the state is changed or left as is)."""
    n = 2 * h
    if rng.random() < 0.1:
        # Add move: join two deficient vertices on opposite sides. Never raises the cost.
        da = [a for a in range(h) if len(adjA[a]) < d]
        db = [b for b in range(h) if len(adjB[b]) < d]
        if da and db:
            a = rng.choice(da)
            b = rng.choice(db)
            if b not in adjA[a]:
                adjA[a].add(b)
                adjB[b].add(a)
                E.append((a, b))
                return _cost(n, h, adjA, adjB, D)
        return cost

    # Swap move: (a,b),(a2,b2) -> (a,b2),(a2,b). Degrees are preserved.
    if len(E) < 2:
        return cost
    i = rng.randrange(len(E))
    j = rng.randrange(len(E))
    if i == j:
        return cost
    a, b = E[i]
    a2, b2 = E[j]
    if a == a2 or b == b2 or b2 in adjA[a] or b in adjA[a2]:
        return cost
    adjA[a].discard(b)
    adjB[b].discard(a)
    adjA[a2].discard(b2)
    adjB[b2].discard(a2)
    adjA[a].add(b2)
    adjB[b2].add(a)
    adjA[a2].add(b)
    adjB[b].add(a2)
    E[i] = (a, b2)
    E[j] = (a2, b)
    nc = _cost(n, h, adjA, adjB, D)
    if nc <= cost or rng.random() < math.exp(-(nc - cost) / T):
        return nc
    # Revert the swap.
    adjA[a].discard(b2)
    adjB[b2].discard(a)
    adjA[a2].discard(b)
    adjB[b].discard(a2)
    adjA[a].add(b)
    adjB[b].add(a)
    adjA[a2].add(b2)
    adjB[b2].add(a2)
    E[i] = (a, b)
    E[j] = (a2, b2)
    return cost


def _sa(h, d, D, E, adjA, adjB, rng, cost, deadline):
    """Anneal until cost is 0 or the deadline passes. Returns the final cost."""
    best_cost = cost
    best_E = list(E)
    since = 0
    T = 0.5 + 0.5 * rng.random()
    while cost > 0:
        if time.monotonic() >= deadline:
            break
        for _ in range(32):
            cost = _step(h, d, D, E, adjA, adjB, rng, cost, T)
            if cost == 0:
                break
        since += 32
        if cost < best_cost:
            best_cost = cost
            best_E = list(E)
            since = 0
        elif since > 3000:
            # Drift control: return to the best state seen at this size.
            E[:] = best_E
            _fill(E, adjA, adjB)
            cost = best_cost
            since = 0
    return cost


def _chain(d, D, rng, deadline, record):
    """Grow a valid graph one vertex per side at a time, repairing with annealing."""
    h = d
    E = [(a, b) for a in range(d) for b in range(d)]  # K_{d,d}
    adjA = [set() for _ in range(h)]
    adjB = [set() for _ in range(h)]
    _fill(E, adjA, adjB)
    while time.monotonic() < deadline:
        _extend(h, E, adjA, adjB, d, rng)
        h += 1
        cost = _cost(2 * h, h, adjA, adjB, D)
        cost = _sa(h, d, D, E, adjA, adjB, rng, cost, deadline)
        if cost != 0:
            return
        record(2 * h, [(a, h + b) for a, b in E])


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fast path: the projective plane meets the Moore bound when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Safe fallback: K_{d,d} has diameter 2.
    n0, e0 = lib.haar_graph(d, range(d))
    state = {"n": n0, "e": e0}

    if D == 2 or d < 2:
        return n0, e0

    def record(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"] = n
            state["e"] = e

    rng = random.Random(seed * 1000003 + d * 101 + D)
    try:
        _chain(d, D, rng, deadline, record)
    except Exception:
        pass

    n, e = state["n"], state["e"]
    if not lib.is_valid(n, e, d, D):
        return n0, e0
    return n, e
