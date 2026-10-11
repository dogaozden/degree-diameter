import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _ara(d):
    """Araujo-Pardo & Lopez graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Helpers.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertices greedily. Adding edges never increases distances."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# NEW IDEA: degree-preserving vertex insertion by 2-switch annealing.
#
# Given a d-regular bipartite graph G of diameter <= D on n vertices, insert one
# new A-vertex x and one new B-vertex y as follows:
#   * pick d edges (a_i, b_i) forming a matching;
#   * delete them, join x to every b_i and y to every a_i.
# The result is still d-regular and bipartite on n+2 vertices, but its diameter
# is usually broken. We then anneal with 2-switches (a1,b1),(a2,b2) ->
# (a1,b2),(a2,b1), which keep every degree and the bipartition, minimising the
# number of vertex pairs at distance > D. A zero-cost state is a valid graph
# with two more vertices than G.
# ----------------------------------------------------------------------------

def _bad_pairs(n, E, D):
    """Number of unordered pairs at distance > D, from an edge list over vertices 0..n-1."""
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _grow_pair(n, edges, d, D, deadline, rng):
    """Try to insert one A-vertex and one B-vertex into a d-regular graph. Returns (n+2, E) or None."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    if any(len(a) != d for a in adj):
        return None
    color = _bipartition(n, [list(a) for a in adj])
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]

    # Choose d edges forming a matching.
    order = list(range(len(E)))
    rng.shuffle(order)
    usedA, usedB, removed = set(), set(), []
    for i in order:
        a, b = E[i]
        if a in usedA or b in usedB:
            continue
        usedA.add(a)
        usedB.add(b)
        removed.append(i)
        if len(removed) == d:
            break
    if len(removed) < d:
        return None

    rem = set(removed)
    x, y = n, n + 1
    E2 = [E[i] for i in range(len(E)) if i not in rem]
    for i in removed:
        a, b = E[i]
        E2.append((a, y))
        E2.append((x, b))

    S = set(E2)
    m = len(E2)
    cur = _bad_pairs(n + 2, E2, D)
    T0, T1 = 2.0, 0.05
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)

    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        T = T0 * (T1 / T0) ** frac

        i, j = rng.randrange(m), rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E2[i]
        a2, b2 = E2[j]
        if a1 == a2 or b1 == b2:
            continue
        e1, e2 = (a1, b2), (a2, b1)
        if e1 in S or e2 in S:
            continue

        E2[i], E2[j] = e1, e2
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add(e1)
        S.add(e2)

        c2 = _bad_pairs(n + 2, E2, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
        else:
            E2[i], E2[j] = (a1, b1), (a2, b2)
            S.discard(e1)
            S.discard(e2)
            S.add((a1, b1))
            S.add((a2, b2))

    return n + 2, E2


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 0.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Record-level constructions.
    ara = _ara(d)
    if ara is not None:
        consider(ara[0], ara[1])
    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    bound = lib._moore_bound(d, D)
    if best_n >= bound:
        return best

    # Growth by degree-preserving insertion.
    cur_n = best_n
    cur_e = _saturate(best_n, best[1], d, rng)
    degs = [0] * cur_n
    for u, v in cur_e:
        degs[u] += 1
        degs[v] += 1
    if any(x != d for x in degs):
        return best  # insertion needs a d-regular base

    while time.monotonic() < deadline and cur_n < bound:
        remaining = deadline - time.monotonic()
        slice_end = min(deadline, time.monotonic() + max(2.0, 0.3 * remaining))
        res = _grow_pair(cur_n, cur_e, d, D, slice_end, rng)
        if res is None:
            continue
        n2, e2 = res
        if not lib.is_valid(n2, e2, d, D):
            continue
        cur_n, cur_e = n2, e2
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
