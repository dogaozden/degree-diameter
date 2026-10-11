import random
import time

import lib


def _parent_search(d, D, seed, deadline):
    """Random Haar-graph search (the previous approach), used only as a fallback."""
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def _largest_prime_power_leq(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _best_construction_d3(d):
    """Try several algebraic constructions for diameter 3 and keep the largest valid one.

    - Araujo-Pardo & Lopez graph for q = d-2 (degree q+2 = d): 2(q^2+q+5) vertices.
    - Projective plane incidence PG(2, d-1) when d-1 is a prime power (degree d).
    - Projective plane incidence PG(2, q) for the largest prime power q <= d-1.
    Every candidate is checked with lib.is_valid before it is accepted.
    """
    makers = []
    q1 = d - 1
    if q1 >= 2 and lib.is_prime_power(q1):
        makers.append(lambda q=q1: lib.projective_plane_incidence(q))
    q2 = d - 2
    if q2 >= 3 and lib.is_prime_power(q2):
        makers.append(lambda q=q2: lib.araujo_lopez_graph(q))
    q3 = _largest_prime_power_leq(d - 1)
    if q3 is not None and q3 >= 2:
        makers.append(lambda q=q3: lib.projective_plane_incidence(q))

    best = None
    for make in makers:
        try:
            n, edges = make()
            edges = list(edges)
            if lib.is_valid(n, edges, d, 3) and (best is None or n > best[0]):
                best = (n, edges)
        except Exception:
            continue
    return best


def _colors(n, adj):
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


def _extend_d3(n, edges, d, D, rng, deadline):
    """Greedy attempt to add one vertex at a time using spare degree.

    A new vertex x of colour c must be within distance 2 of every colour-c vertex,
    so its chosen neighbours' neighbourhoods should cover that colour class.
    Each candidate addition is accepted only if lib.is_valid still holds.
    """
    edges = list(edges)
    adj = lib.adjacency(n, edges)
    color = _colors(n, adj)
    fails = 0
    while time.monotonic() < deadline and fails < 5:
        c = rng.randint(0, 1)
        slack = [v for v in range(n) if color[v] != c and len(adj[v]) < d]
        if not slack:
            break
        rng.shuffle(slack)
        target = sum(1 for v in range(n) if color[v] == c)
        covered = set()
        chosen = []
        while len(chosen) < d and len(covered) < target:
            best, bg = None, 0
            for s in slack:
                if s in chosen:
                    continue
                g = sum(1 for x in adj[s] if x not in covered)
                if g > bg:
                    best, bg = s, g
            if best is None:
                break
            chosen.append(best)
            covered.update(adj[best])
        if not chosen:
            fails += 1
            continue
        cand = edges + [(n, s) for s in chosen]
        if lib.is_valid(n + 1, cand, d, D):
            edges = cand
            adj.append(sorted(chosen))
            for s in chosen:
                adj[s].append(n)
            color.append(c)
            n += 1
            fails = 0
        else:
            fails += 1
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 3:
        best = _best_construction_d3(d)
        if best is None:
            best = _parent_search(d, D, seed, start + 0.6 * time_limit)
        else:
            n, edges = best
            n, edges = _extend_d3(n, edges, d, D, rng, start + 0.7 * time_limit)
            best = (n, edges)
    else:
        best = _parent_search(d, D, seed, start + 0.6 * time_limit)

    n, edges = best
    if not lib.is_valid(n, edges, d, D):
        n, edges = lib.haar_graph(d, range(d))
        if not lib.is_valid(n, edges, d, D):
            n, edges = 2, [(0, 1)]
    return n, list(edges)
