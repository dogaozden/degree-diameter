import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bipartite edge-switch annealing with vertex growth (D = 3 targets).
#
# State: A-side vertices 0..na-1, B-side vertices 0..nb-1, adjacency as sets.
# Moves preserve bipartiteness and the degree cap d:
#   switch (2-opt), endpoint move on either side, and add-edge between spare vertices.
# Cost = number of unordered pairs at distance > D (zero means valid).
# The search grows the vertex count by one vertex per side whenever cost reaches 0,
# and restores the last valid snapshot with a larger budget when it stalls.
# Every accepted graph is checked with lib.is_valid; the fallback is always valid.
# ----------------------------------------------------------------------------


def _sides(n, edges):
    """Two-colouring of the graph, or None if it is not bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _state_from(n, edges, color):
    """Convert (n, edges) with a 2-colouring into side sizes and adjacency sets."""
    idx = [0] * n
    na = nb = 0
    for v in range(n):
        if color[v] == 0:
            idx[v] = na
            na += 1
        else:
            idx[v] = nb
            nb += 1
    adjA = [set() for _ in range(na)]
    adjB = [set() for _ in range(nb)]
    for u, v in edges:
        if color[u] == 1:
            u, v = v, u
        a, b = idx[u], idx[v]
        adjA[a].add(b)
        adjB[b].add(a)
    return na, nb, adjA, adjB


def _edge_list(na, adjA):
    """Edges as (A-id, na + B-id) pairs."""
    return [(a, na + b) for a in range(na) for b in sorted(adjA[a])]


def _bad(na, nb, adjA, adjB, D):
    """Number of unordered vertex pairs at distance more than D."""
    n = na + nb
    nbr = [[na + b for b in adjA[a]] for a in range(na)]
    nbr += [list(adjB[b]) for b in range(nb)]
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _apply(ops, adjA, adjB):
    """Apply a list of (sign, a, b) edge operations: +1 adds, -1 removes."""
    for s, a, b in ops:
        if s > 0:
            adjA[a].add(b)
            adjB[b].add(a)
        else:
            adjA[a].discard(b)
            adjB[b].discard(a)


def _propose(na, nb, adjA, adjB, d, rng):
    """Return a list of degree-safe edge operations, or None if the proposal is infeasible."""
    r = rng.random()
    if r < 0.4:
        # 2-switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1)
        a1 = rng.randrange(na)
        a2 = rng.randrange(na)
        if a1 == a2 or not adjA[a1] or not adjA[a2]:
            return None
        b1 = rng.choice(tuple(adjA[a1]))
        b2 = rng.choice(tuple(adjA[a2]))
        if b2 in adjA[a1] or b1 in adjA[a2]:
            return None
        return [(-1, a1, b1), (-1, a2, b2), (1, a1, b2), (1, a2, b1)]
    if r < 0.6:
        # Move an A-side edge endpoint from a1 to a spare a2.
        spare = [a for a in range(na) if len(adjA[a]) < d]
        a1 = rng.randrange(na)
        if not spare or not adjA[a1]:
            return None
        a2 = rng.choice(spare)
        b1 = rng.choice(tuple(adjA[a1]))
        if a2 == a1 or b1 in adjA[a2]:
            return None
        return [(-1, a1, b1), (1, a2, b1)]
    if r < 0.8:
        # Move a B-side edge endpoint from b1 to a spare b2.
        spare = [b for b in range(nb) if len(adjB[b]) < d]
        b1 = rng.randrange(nb)
        if not spare or not adjB[b1]:
            return None
        b2 = rng.choice(spare)
        a1 = rng.choice(tuple(adjB[b1]))
        if b2 == b1 or a1 in adjB[b2]:
            return None
        return [(-1, a1, b1), (1, a1, b2)]
    # Add an edge between spare vertices on opposite sides.
    spA = [a for a in range(na) if len(adjA[a]) < d]
    spB = [b for b in range(nb) if len(adjB[b]) < d]
    if not spA or not spB:
        return None
    a = rng.choice(spA)
    b = rng.choice(spB)
    if b in adjA[a]:
        return None
    return [(1, a, b)]


def _anneal(na, nb, adjA, adjB, d, D, rng, deadline, budget):
    """Threshold-accepting search on the current state. Returns the final cost."""
    cost = _bad(na, nb, adjA, adjB, D)
    it = 0
    while cost > 0 and it < budget:
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = 1.2 * (0.02 ** (it / budget))
        it += 1
        ops = _propose(na, nb, adjA, adjB, d, rng)
        if ops is None:
            continue
        _apply(ops, adjA, adjB)
        c2 = _bad(na, nb, adjA, adjB, D)
        limit = cost - T * math.log(1.0 - rng.random())
        if c2 <= limit:
            cost = c2
        else:
            _apply([(-s, a, b) for s, a, b in reversed(ops)], adjA, adjB)
    return cost


def _moore(d, D):
    """Moore bound for bipartite graphs with max degree d and diameter D (d >= 3)."""
    return 2 * sum((d - 1) ** i for i in range(D))


def _grow_search(d, D, n, edges, rng, deadline, best):
    """Grow a valid bipartite graph one vertex per side at a time, keeping every valid result."""
    color = _sides(n, edges)
    if color is None:
        return best
    na, nb, adjA, adjB = _state_from(n, edges, color)
    snapA = [set(s) for s in adjA]
    snapB = [set(s) for s in adjB]
    snap_na, snap_nb = na, nb
    budget = 3000
    limit_n = _moore(d, D)

    while time.monotonic() < deadline:
        cost = _anneal(na, nb, adjA, adjB, d, D, rng, deadline, budget)
        if cost == 0:
            N = na + nb
            E = _edge_list(na, adjA)
            if N > best[0] and lib.is_valid(N, E, d, D):
                best = (N, E)
            snapA = [set(s) for s in adjA]
            snapB = [set(s) for s in adjB]
            snap_na, snap_nb = na, nb
            budget = 3000
        else:
            adjA = [set(s) for s in snapA]
            adjB = [set(s) for s in snapB]
            na, nb = snap_na, snap_nb
            budget = min(budget * 2, 100000)

        if na + nb + 2 > limit_n:
            break
        adjA.append(set())
        adjB.append(set())
        na += 1
        nb += 1
    return best


def _candidates(d, D):
    """Known algebraic constructions valid for D >= 3."""
    out = []
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                out.append(lib.projective_plane_incidence(q))
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                out.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, which is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    for n, e in _candidates(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3 and d >= 3:
        try:
            best = _grow_search(d, D, best[0], best[1], rng, deadline, best)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])
    return best
