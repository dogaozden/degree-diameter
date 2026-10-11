import random
import time

import lib


def _base_graph(q):
    """Incidence graph of PG(2, q): points 0..m-1 (side 0), lines m..2m-1 (side 1). Diameter 3."""
    n, edges = lib.projective_plane_incidence(q)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    half = n // 2
    side = [0 if v < half else 1 for v in range(n)]
    return adj, side


def _try_add(adj, side, s, d, rng, noise):
    """Neighbour list for a new vertex on side s that dominates every existing side-s vertex, or None.

    Invariant used: if every existing vertex on side s has a neighbour in N(v), and v is attached
    only to side 1-s, then all distances from v are at most 3 and all old distances are unchanged
    (adding a vertex never lengthens paths). Hence diameter <= 3 is preserved by induction.
    """
    uncovered = {v for v in range(len(adj)) if side[v] == s}
    if not uncovered:
        return None
    cov = {y: len(adj[y]) for y in range(len(adj))
           if side[y] != s and adj[y] and len(adj[y]) < d}
    chosen = []
    while uncovered:
        if len(chosen) >= d or not cov:
            return None
        best = None
        bs = -1.0
        for y, c in cov.items():
            if c <= 0:
                continue
            sc = c + noise * rng.random()
            if sc > bs:
                bs = sc
                best = y
        if best is None:
            return None
        chosen.append(best)
        del cov[best]
        for x in adj[best]:
            if x in uncovered:
                uncovered.discard(x)
                for y in adj[x]:
                    if y in cov:
                        cov[y] -= 1
    return chosen


def _grow(adj, side, d, cap, rng, noise, deadline, tries):
    """Greedily append dominating new vertices on either side while spare degree allows."""
    while len(adj) < cap and time.monotonic() < deadline:
        order = [0, 1]
        rng.shuffle(order)
        placed = False
        for s in order:
            for _ in range(tries):
                nb = _try_add(adj, side, s, d, rng, noise)
                if nb is not None:
                    v = len(adj)
                    adj.append(set(nb))
                    side.append(s)
                    for y in nb:
                        adj[y].add(v)
                    placed = True
                    break
            if placed:
                break
        if not placed:
            break


def _saturate(adj, side, d, rng):
    """Add every missing cross-side edge whose endpoints both have spare degree.

    Extra cross edges keep the graph bipartite and can only shorten distances.
    """
    xs = [v for v in range(len(adj)) if side[v] == 0 and len(adj[v]) < d]
    ys = [v for v in range(len(adj)) if side[v] == 1 and len(adj[v]) < d]
    pairs = [(x, y) for x in xs for y in ys if y not in adj[x]]
    rng.shuffle(pairs)
    for x, y in pairs:
        if len(adj[x]) < d and len(adj[y]) < d and y not in adj[x]:
            adj[x].add(y)
            adj[y].add(x)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback[0], fallback[1]
    if D == 2:
        return best_n, best_e

    # Diameter-3 family: projective-plane bases grown by dominating vertex additions.
    qs = sorted((q for q in range(2, d) if lib.is_prime_power(q)), reverse=True)[:3]
    if not qs:
        return best_n, best_e
    bases = [_base_graph(q) for q in qs]
    cap = lib.moore_bound(d, D)

    for badj, _ in bases:
        n0 = len(badj)
        if n0 > best_n:
            e0 = [(u, v) for u in range(n0) for v in badj[u] if u < v]
            if lib.is_valid(n0, e0, d, D):
                best_n, best_e = n0, e0

    k = 0
    stale = 0
    while time.monotonic() < deadline and stale < 40:
        badj, bside = bases[k % len(bases)]
        k += 1
        adj = [set(s) for s in badj]
        side = list(bside)
        noise = rng.choice([0.3, 0.8, 1.5, 3.0])
        _grow(adj, side, d, cap, rng, noise, deadline, tries=3)
        _saturate(adj, side, d, rng)
        n = len(adj)
        if n > best_n:
            edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
            if lib.is_valid(n, edges, d, D):
                best_n, best_e = n, edges
                stale = 0
                continue
        stale += 1

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback[0], fallback[1]
    return best_n, best_e
