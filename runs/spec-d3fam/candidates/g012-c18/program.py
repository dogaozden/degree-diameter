"""Repair-search growth for D = 3 targets (and any D >= 3).

Start from the best valid algebraic base (Araujo-Pardo & Lopez record, or the
projective-plane incidence graph). Repeatedly add one A-vertex and one B-vertex,
seeding their degrees by stealing edges from the existing graph. Then run
simulated annealing with degree-preserving double-edge swaps, minimising the
number of vertex pairs at distance > D. A level is accepted only when the cost
reaches zero. Every returned graph is checked with lib.is_valid, and the
fallback K_{d,d} (diameter 2) is always available.

Caveat: this is a heuristic. It was not run against the records here.
"""
import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph when q = d - 2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


def _color(n, edges):
    """Proper 2-colouring of a bipartite graph, or None if it is not bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
                elif col[v] == col[u]:
                    return None
    return col


def _cost(n, E, D):
    """Number of unordered vertex pairs at distance > D (0 means diameter <= D)."""
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _add_pair(n, E, d, rng):
    """Append new vertices x (side 0) and y (side 1), each of degree d, by stealing edges.

    Stealing edge (a, b) and replacing it with (a, y) and (x, b) keeps every
    existing degree unchanged. Modifies E in place.
    """
    x, y = n, n + 1
    nx, ny = set(), set()
    tries = 0
    while len(nx) < d and tries < 200000 and E:
        tries += 1
        i = rng.randrange(len(E))
        a, b = E[i]
        if b in nx or a in ny:
            continue
        E[i] = (a, y)
        E.append((x, b))
        nx.add(b)
        ny.add(a)
    return len(nx) == d


def _repair_level(n, E, d, D, deadline, rng):
    """Anneal degree-preserving swaps until diameter <= D. Returns E or None."""
    ES = set(E)
    m = len(E)
    if m < 2:
        return None
    cost = _cost(n, E, D)
    T0, T1 = 1.0, 0.05
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - start) / span
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        if (a, e) in ES or (c, b) in ES:
            continue
        E[i] = (a, e)
        E[j] = (c, b)
        ES.discard((a, b))
        ES.discard((c, e))
        ES.add((a, e))
        ES.add((c, b))
        c2 = _cost(n, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            E[i] = (a, b)
            E[j] = (c, e)
            ES.discard((a, e))
            ES.discard((c, b))
            ES.add((a, b))
            ES.add((c, e))
    return E


def _grow(n, E, d, D, deadline, rng):
    """Repeatedly add a vertex pair and repair; returns the last valid (n, E)."""
    while time.monotonic() < deadline:
        E2 = list(E)
        if not _add_pair(n, E2, d, rng):
            break
        level_deadline = time.monotonic() + 0.6 * (deadline - time.monotonic())
        res = _repair_level(n + 2, E2, d, D, level_deadline, rng)
        if res is None:
            break
        n, E = n + 2, res
    return n, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = (fb_n, fb_e)
    if D == 2 or d < 2:
        return best

    cands = []
    rec = _araujo(d)
    if rec is not None:
        cands.append(rec)
    pg = _best_pg(d)
    if pg is not None:
        cands.append(pg)

    valid = []
    for n0, e0 in cands:
        if lib.is_valid(n0, e0, d, D):
            valid.append((n0, e0))
            if n0 > best[0]:
                best = (n0, e0)

    if valid:
        base_n, base_e = max(valid, key=lambda t: t[0])
        col = _color(base_n, base_e)
        if col is not None:
            E = [(u, v) if col[u] == 0 else (v, u) for u, v in base_e]
            gn, gE = _grow(base_n, E, d, D, deadline, rng)
            if gn > best[0]:
                out_e = list(gE)
                if lib.is_valid(gn, out_e, d, D):
                    best = (gn, out_e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = (fb_n, fb_e)
    return best
