import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: a different search space for the weak cases. Instead of
# algebraic lifts, anneal directly over simple d-regular bipartite graphs.
#
# State: a d-regular bipartite graph with h vertices per side, initialised as
# a circulant (a in A joins b in B for shifts 0..d-1). Moves are edge switches
# (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keep degrees, bipartiteness and
# simplicity. Cost = number of ordered (vertex, vertex) pairs at distance > D.
# The order is grown one step at a time while annealing still reaches cost 0.
# ----------------------------------------------------------------------------


def _cost(n, adj, D):
    """Ordered pairs at distance > D, via bitmask ball expansion."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _unlink(adj, a, b):
    adj[a].discard(b)
    adj[b].discard(a)


def _link(adj, a, b):
    adj[a].add(b)
    adj[b].add(a)


def _anneal(d, D, h, rng, deadline):
    """Simulated annealing on edge switches for a d-regular bipartite graph on 2h vertices.

    Returns (n, edges) on cost 0, else None.
    """
    n = 2 * h
    E = []
    Eset = set()
    for a in range(h):
        for s in range(d):
            b = h + (a + s) % h
            E.append((a, b))
            Eset.add((a, b))
    adj = [set() for _ in range(n)]
    for a, b in E:
        _link(adj, a, b)

    cur = _cost(n, adj, D)
    T = 2.0
    it = 0
    while cur > 0:
        it += 1
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in Eset or (a2, b1) in Eset:
            continue
        _unlink(adj, a1, b1)
        _unlink(adj, a2, b2)
        _link(adj, a1, b2)
        _link(adj, a2, b1)
        c2 = _cost(n, adj, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            Eset.discard((a1, b1))
            Eset.discard((a2, b2))
            Eset.add((a1, b2))
            Eset.add((a2, b1))
            E[i] = (a1, b2)
            E[j] = (a2, b1)
            cur = c2
        else:
            _unlink(adj, a1, b2)
            _unlink(adj, a2, b1)
            _link(adj, a1, b1)
            _link(adj, a2, b2)
        T = max(0.05, T * 0.9995)

    if cur == 0:
        return n, list(E)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
        return best

    moore = lib._moore_bound(d, D)
    rng = random.Random(seed * 1000003 + d * 101 + D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Grow the bipartition size h; each success adds a small step.
    h = max(d, 60)
    step_ok = True
    while step_ok and time.monotonic() < deadline:
        if 2 * h > moore:
            break
        remaining = deadline - time.monotonic()
        slice_end = min(deadline, time.monotonic() + max(0.5, 0.4 * remaining))
        res = _anneal(d, D, h, rng, slice_end)
        if res is None:
            step_ok = False
            break
        consider(res[0], res[1])
        h += max(1, h // 25)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
