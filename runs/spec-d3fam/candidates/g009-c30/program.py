import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: record Araujo-Pardo & Lopez graph (d-2 prime power) and plain PG(2,q).
# ----------------------------------------------------------------------------

def _araujo(d):
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New idea: "pair insertion + annealed double-edge-swap repair".
#
# Take a valid bipartite graph with max degree d. Pick a matching of d-1 edges
# (a_i, b_i), delete them, and add one new A-vertex x and one new B-vertex y.
# Join x to every b_i and y to every a_i, and join x to y. Every old vertex keeps
# its degree and both new vertices reach degree exactly d. The graph is now
# (n+2)-order but may violate the diameter bound. Simulated annealing then
# applies bipartite double-edge swaps (which preserve all degrees and the
# bipartition) to minimize the number of pairs at distance > D. Success gives a
# valid graph with two more vertices, and the process repeats from it.
# ----------------------------------------------------------------------------

def _colors(n, edges):
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
    return color


def _normalize(edges, color):
    """Orient each edge as (A-vertex, B-vertex), where A is colour 0."""
    return [(u, v) if color[u] == 0 else (v, u) for u, v in edges]


def _insert_pair(n, E, d, rng):
    """Remove a random matching of size d-1 and add an (A, B) vertex pair as described above."""
    order = list(range(len(E)))
    rng.shuffle(order)
    usedA, usedB, match = set(), set(), []
    for i in order:
        if len(match) == d - 1:
            break
        a, b = E[i]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        match.append(i)
    if len(match) < d - 1:
        return None
    drop = set(match)
    x, y = n, n + 1
    newE = [e for k, e in enumerate(E) if k not in drop]
    for i in match:
        a, b = E[i]
        newE.append((x, b))
        newE.append((a, y))
    newE.append((x, y))
    return n + 2, newE


def _anneal(n, E, D, deadline, rng, T0=1.0, T1=0.1):
    """Double-edge-swap annealing on normalized edge list E; returns E when diameter <= D, else None."""
    Eset = set(E)
    m = len(E)
    cost = lib.bad_pairs(n, E, D)
    if cost == 0:
        return E
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        f1, f2 = (a, e), (c, b)
        if f1 in Eset or f2 in Eset:
            continue
        E[i], E[j] = f1, f2
        Eset.discard((a, b))
        Eset.discard((c, e))
        Eset.add(f1)
        Eset.add(f2)
        c2 = lib.bad_pairs(n, E, D)
        T = T0 * (T1 / T0) ** (min(1.0, (now - t0) / span))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            E[i], E[j] = (a, b), (c, e)
            Eset.discard(f1)
            Eset.discard(f2)
            Eset.add((a, b))
            Eset.add((c, e))
    return E if cost == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 0.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and max degree d.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        for base in (_araujo(d), _best_pg(d)):
            if base is not None:
                consider(base[0], base[1])

    # Repair-based growth from the current best graph.
    if d >= 3 and time.monotonic() < deadline:
        cur_n, cur_E = best
        while time.monotonic() < deadline - 1.0:
            color = _colors(cur_n, cur_E)
            E = _normalize(cur_E, color)
            ins = _insert_pair(cur_n, E, d, rng)
            if ins is None:
                break
            n2, E2 = ins
            remaining = deadline - time.monotonic()
            slice_end = min(deadline, time.monotonic() + max(1.0, remaining / 3))
            out = _anneal(n2, E2, D, slice_end, rng)
            if out is not None and lib.is_valid(n2, out, d, D):
                cur_n, cur_E = n2, out
                consider(n2, out)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
