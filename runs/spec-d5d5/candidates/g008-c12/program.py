import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Different construction: degree-preserving bipartite edge-swap annealing.
#
# The graph is kept d-regular and bipartite (A-side ids are the first
# coordinate of each edge). Each move is a double edge swap, which preserves
# all degrees and the bipartition. Growth adds two vertices (one per side)
# by splitting d disjoint edges, so the graph stays d-regular. Annealing
# minimises the number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------


def _cost(n, adj, D):
    """Ordered count of vertex pairs at distance > D (0 means diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - bin(r).count("1") for r in reach)


def _replace(E, S, adj, idx, new):
    """Replace edge E[idx] by `new`, keeping the edge set S and adjacency sets in sync."""
    a, b = E[idx]
    S.discard((a, b))
    adj[a].discard(b)
    adj[b].discard(a)
    a2, b2 = new
    E[idx] = (a2, b2)
    S.add((a2, b2))
    adj[a2].add(b2)
    adj[b2].add(a2)


def _grow(E, S, adj, n, d, rng):
    """Add one A-vertex and one B-vertex, each of degree d, keeping d-regularity.

    Picks d pairwise-disjoint edges (a_i, b_i), replaces each by (a_i, B2),
    and adds (A2, b_i). Returns the new vertex count, or None if no such
    matching of size d is found.
    """
    order = list(range(len(E)))
    rng.shuffle(order)
    usedA, usedB, chosen = set(), set(), []
    for i in order:
        a, b = E[i]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        chosen.append(i)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    A2, B2 = n, n + 1
    adj.append(set())
    adj.append(set())
    removed = [E[i] for i in chosen]
    for a, b in removed:
        S.discard((a, b))
        adj[a].discard(b)
        adj[b].discard(a)
    for i, (a, b) in zip(chosen, removed):
        E[i] = (a, B2)
        S.add((a, B2))
        adj[a].add(B2)
        adj[B2].add(a)
        E.append((A2, b))
        S.add((A2, b))
        adj[A2].add(b)
        adj[b].add(A2)
    return n + 2


def _anneal(E, S, adj, n, D, rng, deadline):
    """Double-edge-swap annealing until cost is 0 or the deadline passes. Returns final cost."""
    cur = _cost(n, adj, D)
    while cur > 0 and time.monotonic() < deadline and len(E) >= 2:
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        old_i, old_j = E[i], E[j]
        _replace(E, S, adj, i, (a1, b2))
        _replace(E, S, adj, j, (a2, b1))
        c2 = _cost(n, adj, D)
        delta = c2 - cur
        T = max(1.0, 0.03 * cur)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
        else:
            _replace(E, S, adj, j, old_j)
            _replace(E, S, adj, i, old_i)
    return cur


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is d-regular bipartite.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    # D = 3: the projective plane incidence graph is optimal when d-1 is a prime power.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
        if best[0] >= moore:
            return best

    # Growth starts from the current best d-regular bipartite graph.
    n0, e0 = best
    E = [(min(a, b), max(a, b)) for a, b in e0]
    S = set(E)
    adj = [set() for _ in range(n0)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    n = n0

    while time.monotonic() < deadline and n < moore:
        grown = _grow(E, S, adj, n, d, rng)
        if grown is None:
            break
        n = grown
        cur = _anneal(E, S, adj, n, D, rng, deadline)
        if cur != 0:
            break
        if n > best[0]:
            cand_edges = [(a, b) for a, b in E]
            if lib.is_valid(n, cand_edges, d, D):
                best = (n, cand_edges)
            else:
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
