import math
import random
import time

import lib


def _reach_cost(n, adj, D):
    """Ordered vertex pairs at distance > D (0 means diameter <= D and connected)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _set_edges(adj, E, eset, i1, i2, new1, new2):
    """Replace the current edges E[i1], E[i2] by new1, new2, keeping adj and eset in sync."""
    a1, b1 = E[i1]
    a2, b2 = E[i2]
    eset.discard((a1, b1))
    eset.discard((a2, b2))
    adj[a1].remove(b1)
    adj[b1].remove(a1)
    adj[a2].remove(b2)
    adj[b2].remove(a2)
    E[i1] = new1
    E[i2] = new2
    x1, y1 = new1
    x2, y2 = new2
    eset.add(new1)
    eset.add(new2)
    adj[x1].append(y1)
    adj[y1].append(x1)
    adj[x2].append(y2)
    adj[y2].append(x2)


def _anneal(h, d, D, rng, deadline, T0=3.0, T1=0.2):
    """Simulated annealing over d-regular bipartite graphs on h + h vertices.

    Moves are bipartite double-edge swaps, which preserve regularity and bipartiteness.
    Returns an edge list of diameter <= D, or None if the deadline passes first.
    """
    n = 2 * h
    E = [(i, h + (i + j) % h) for i in range(h) for j in range(d)]
    eset = set(E)
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    cost = _reach_cost(n, adj, D)
    if cost == 0:
        return list(E)
    m = len(E)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = T0
    it = 0
    while cost > 0:
        it += 1
        if (it & 31) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = (now - t0) / span
            T = T0 * (T1 / T0) ** frac
        i1 = rng.randrange(m)
        i2 = rng.randrange(m)
        if i1 == i2:
            continue
        a1, b1 = E[i1]
        a2, b2 = E[i2]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        _set_edges(adj, E, eset, i1, i2, (a1, b2), (a2, b1))
        c2 = _reach_cost(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            _set_edges(adj, E, eset, i1, i2, (a1, b1), (a2, b2))
    if cost == 0:
        return list(E)
    return None


def _search(d, D, seed, deadline, h_start):
    """Climb the side size h, annealing for each h; return the largest (n, edges) found or None."""
    rng = random.Random(seed)
    best = None
    h = h_start
    fails = 0
    share = 0.35
    while True:
        now = time.monotonic()
        rem = deadline - now
        if rem < 0.2:
            break
        dl = now + max(0.3, share * rem)
        E = _anneal(h, d, D, rng, min(dl, deadline))
        if E is not None:
            best = (2 * h, E)
            h += 1
            fails = 0
            share = 0.35
        else:
            fails += 1
            if fails >= 2:
                break
            share = 0.6
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and max degree d.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 2:
        return best_n, best_e

    # Projective plane incidence graph: optimal for D = 3 when d - 1 is a prime power.
    pg_ok = d >= 3 and lib.is_prime_power(d - 1)
    if pg_ok:
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        if D == 3:
            return best_n, best_e

    # Bipartite d-regular annealing: climb the side size and keep the largest valid graph.
    h_start = 70 if (d == 4 and D == 5) else max(d, 2)
    try:
        res = _search(d, D, seed, deadline, h_start)
        if res is not None:
            consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
