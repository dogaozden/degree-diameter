"""Bipartite degree-bounded graph search: simulated annealing over edge moves, growing the vertex count
whenever the diameter bound is met. Pure Python; no C engine."""
import math
import random
import time

import lib

TIME_FRAC = 0.85       # fraction of time_limit used by the search
STUCK_LIMIT = 6000     # proposals without growth before restarting from the best graph
GROW_PATIENCE = 200    # valid iterations to wait for full degree before growing anyway
TEMP = 0.5             # Metropolis temperature on the change in bad pairs
PAIR_TRIES = 30        # random attempts to find a non-adjacent spare pair


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (bitset BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _adj_from(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _replace(adj, edges, i, new):
    """Replace edge number i by `new`; return the old edge."""
    old = edges[i]
    adj[old[0]].discard(old[1])
    adj[old[1]].discard(old[0])
    adj[new[0]].add(new[1])
    adj[new[1]].add(new[0])
    edges[i] = new
    return old


def _propose(n, adj, edges, idx, new, bad, D, rng):
    """Apply a single-edge replacement; keep it under Metropolis on the bad-pair count."""
    old = _replace(adj, edges, idx, new)
    nb = _bad(n, adj, D)
    dE = nb - bad
    if dE <= 0 or rng.random() < math.exp(-dE / TEMP):
        return nb
    _replace(adj, edges, idx, old)
    return bad


def _search(d, D, rng, deadline, n, side, edges):
    """Anneal a bipartite graph with max degree d; grow by two vertices whenever it is valid.

    Returns (n, edges) for the largest valid graph seen, or None.
    Vertices with side 0 are left, side 1 are right; every edge is stored as (left, right).
    """
    adj = _adj_from(n, edges)
    bad = _bad(n, adj, D)
    best = None
    best_n = 0
    zero_run = 0
    since = 0
    while time.monotonic() < deadline:
        deficit = sum(d - len(a) for a in adj)
        if bad == 0:
            zero_run += 1
            if deficit == 0 or zero_run >= GROW_PATIENCE:
                if n > best_n:
                    best_n = n
                    best = (n, list(side), list(edges))
                side.append(0)
                side.append(1)
                adj.append(set())
                adj.append(set())
                n += 2
                bad = _bad(n, adj, D)
                zero_run = 0
                since = 0
                continue
        else:
            zero_run = 0
        since += 1
        if since > STUCK_LIMIT:
            if best is not None:
                n, side, edges = best[0], list(best[1]), list(best[2])
                adj = _adj_from(n, edges)
                bad = _bad(n, adj, D)
            since = 0
            zero_run = 0
            continue

        spL = [v for v in range(n) if side[v] == 0 and len(adj[v]) < d]
        spR = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]

        # Move A: add an edge between two spare vertices (never increases bad pairs).
        if spL and spR and rng.random() < 0.5:
            x = -1
            y = -1
            for _ in range(PAIR_TRIES):
                x = rng.choice(spL)
                y = rng.choice(spR)
                if y not in adj[x]:
                    break
            else:
                x = -1
            if x >= 0:
                adj[x].add(y)
                adj[y].add(x)
                edges.append((x, y))
                bad = _bad(n, adj, D)
                continue

        # Move C: move one endpoint of a random edge onto a spare vertex (degree sum unchanged).
        if edges and (spL or spR) and rng.random() < 0.5:
            idx = rng.randrange(len(edges))
            c, b = edges[idx]
            if spL and (not spR or rng.random() < 0.5):
                x = rng.choice(spL)
                if x not in adj[b]:
                    bad = _propose(n, adj, edges, idx, (x, b), bad, D, rng)
                continue
            else:
                y = rng.choice(spR)
                if y not in adj[c]:
                    bad = _propose(n, adj, edges, idx, (c, y), bad, D, rng)
                continue

        # Move B: degree-preserving double edge swap (a,b),(c,e) -> (a,e),(c,b).
        if len(edges) >= 2:
            i = rng.randrange(len(edges))
            j = rng.randrange(len(edges))
            if i != j:
                a, b = edges[i]
                c, e = edges[j]
                if e not in adj[a] and b not in adj[c]:
                    old_i = _replace(adj, edges, i, (a, e))
                    old_j = _replace(adj, edges, j, (c, b))
                    nb = _bad(n, adj, D)
                    dE = nb - bad
                    if dE <= 0 or rng.random() < math.exp(-dE / TEMP):
                        bad = nb
                    else:
                        _replace(adj, edges, j, old_j)
                        _replace(adj, edges, i, old_i)

    if bad == 0 and n > best_n:
        best = (n, list(side), list(edges))
    if best is None:
        return None
    return best[0], best[2]


def build(d, D, seed, time_limit):
    start = time.monotonic()

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D                       # even cycle: bipartite, diameter D
        return L, [(i, (i + 1) % L) for i in range(L)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} has diameter 2

    # Moore-extremal shortcut for D = 3 when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    fallback = lib.haar_graph(d, range(d))   # K_{d,d}, always valid for D >= 2
    deadline = start + max(0.5, TIME_FRAC * time_limit - 1.0)
    rng = random.Random(seed * 7919 + 13 * d + D)

    # Start from K_{d,d} and grow by annealing.
    n = 2 * d
    side = [0] * d + [1] * d
    edges = [(i, d + j) for i in range(d) for j in range(d)]
    try:
        res = _search(d, D, rng, deadline, n, side, edges)
    except Exception:
        res = None

    if res is not None:
        n2, e2 = res
        if n2 > fallback[0] and lib.is_valid(n2, e2, d, D):
            return n2, e2
    return fallback
