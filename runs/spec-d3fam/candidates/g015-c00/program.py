"""Bold variant: degree-preserving annealing growth from several diameter-D bipartite seeds.

Seeds: PG(2,q) incidence (spare degree 1 when q+1 < d), Araujo-Pardo & Lopez graph
(when d-2 is a prime power, D = 3), and K_{d,d}. From each seed, two vertices (one per
side) are added at a time, and simulated annealing over edge moves (add, 2-switch,
endpoint relocation) tries to restore diameter <= D. Every candidate is checked with
lib.is_valid before it is kept, and the largest valid graph wins; K_{d,d} is the fallback.
"""
import math
import random
import time

import lib


def _kdd(d):
    """K_{d,d}: valid for every D >= 2, used as the safe fallback."""
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


def _largest_pg_q(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph when d - 2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


def _two_color(n, adj):
    """Two-colouring of the graph, or None if it is not bipartite."""
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


def _bad(n, adj, D):
    """Number of ordered pairs at distance > D (unreachable counts). Zero means diameter <= D."""
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


def _rand_edge(adj, side0, rng):
    """Random edge (a, b) with a in side0, or None if no edge found quickly."""
    for _ in range(16):
        a = rng.choice(side0)
        if adj[a]:
            return a, rng.choice(tuple(adj[a]))
    return None


def _apply(adj, ops):
    for op, a, b in ops:
        if op == '-':
            adj[a].discard(b)
            adj[b].discard(a)
        else:
            adj[a].add(b)
            adj[b].add(a)


def _undo(adj, ops):
    for op, a, b in reversed(ops):
        if op == '-':
            adj[a].add(b)
            adj[b].add(a)
        else:
            adj[a].discard(b)
            adj[b].discard(a)


def _anneal(n, adj, sides, d, D, rng, deadline, iters, T0, T1):
    """Simulated annealing on cross-side edges. Returns True once diameter <= D holds."""
    cost = _bad(n, adj, D)
    if cost == 0:
        return True
    for it in range(iters):
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters - 1))
        r = rng.random()
        if r < 0.25:
            # Add a cross edge between two deficient vertices.
            c0 = [v for v in sides[0] if len(adj[v]) < d]
            c1 = [v for v in sides[1] if len(adj[v]) < d]
            if not c0 or not c1:
                continue
            a = rng.choice(c0)
            b = rng.choice(c1)
            if b in adj[a]:
                continue
            ops = [('+', a, b)]
        elif r < 0.6:
            # Degree-preserving 2-switch.
            e1 = _rand_edge(adj, sides[0], rng)
            e2 = _rand_edge(adj, sides[0], rng)
            if e1 is None or e2 is None:
                continue
            a1, b1 = e1
            a2, b2 = e2
            if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
                continue
            ops = [('-', a1, b1), ('-', a2, b2), ('+', a1, b2), ('+', a2, b1)]
        else:
            # Move one endpoint of an edge to a deficient vertex on the same side.
            e = _rand_edge(adj, sides[0], rng)
            if e is None:
                continue
            a, b = e
            if rng.random() < 0.5:
                cands = [v for v in sides[0] if v != a and len(adj[v]) < d and v not in adj[b]]
                if not cands:
                    continue
                ops = [('-', a, b), ('+', rng.choice(cands), b)]
            else:
                cands = [v for v in sides[1] if v != b and len(adj[v]) < d and v not in adj[a]]
                if not cands:
                    continue
                ops = [('-', a, b), ('+', a, rng.choice(cands))]
        _apply(adj, ops)
        c2 = _bad(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if cost == 0:
                return True
        else:
            _undo(adj, ops)
    return cost == 0


def _search(n, edges, d, D, deadline, rng, consider):
    """Grow a valid seed graph two vertices at a time, repairing each step by annealing."""
    if n > 800:
        return
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _two_color(n, adj)
    if color is None or _bad(n, adj, D) != 0:
        return
    good = (n, [(u, v) for u in range(n) for v in adj[u] if u < v], color)
    while time.monotonic() < deadline:
        gn, ge, gc = good
        n2 = gn + 2
        adj = [set() for _ in range(n2)]
        for u, v in ge:
            adj[u].add(v)
            adj[v].add(u)
        color = gc + [0, 1]
        sides = [[v for v in range(n2) if color[v] == 0],
                 [v for v in range(n2) if color[v] == 1]]
        if _anneal(n2, adj, sides, d, D, rng, deadline, 3000, 3.0, 0.3):
            e2 = [(u, v) for u in range(n2) for v in adj[u] if u < v]
            good = (n2, e2, color)
            consider(n2, e2)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)
    best = list(_kdd(d))  # safe fallback, valid for D >= 2

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    consider(best[0], best[1])

    # Seed graphs, in priority order.
    seeds = []
    if D >= 3:
        q = _largest_pg_q(d)
        if q is not None:
            seeds.append(lib.projective_plane_incidence(q))
        if D == 3:
            ara = _araujo(d)
            if ara is not None:
                seeds.append(ara)
    seeds.append(_kdd(d))

    for n, e in seeds:
        consider(n, e)

    # Give each seed a proportional share of the remaining time.
    weights = {1: [1.0], 2: [0.6, 0.4], 3: [0.5, 0.25, 0.25]}[len(seeds)]
    rng_master = random.Random(seed * 7919 + d * 31 + D)
    for i, (n, e) in enumerate(seeds):
        now = time.monotonic()
        if now >= deadline:
            break
        frac = weights[i] / sum(weights[i:])
        sub_deadline = now + (deadline - now) * frac
        _search(n, e, d, D, sub_deadline, random.Random(rng_master.random()), consider)

    return best[0], list(best[1])
