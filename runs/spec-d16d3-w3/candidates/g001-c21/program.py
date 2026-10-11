import random
import time

import lib


# ---------------------------------------------------------------------------
# New construction: conic extension of PG(2, q).
#
# Take PG(2, q) with q = largest prime power with q + 1 <= d, so every vertex
# has degree q + 1 and the spare degree is d - q - 1 >= 2. Let C be the conic
# {(1, t, t^2)} plus (0, 0, 1), which has q + 1 points. Every line meets C in at
# most 2 points, and dually every point lies on at most 2 lines of the dual conic.
#
#   * For each conic point c, add a new "point" vertex joined to all q + 1 lines
#     through c.
#   * For each dual conic line M, add a new "line" vertex joined to all q + 1
#     points on M.
#
# Old lines gain at most 2 new neighbours and old points gain at most 2, so the
# max degree is q + 3 <= d. The new vertices give 2(q + 1) extra vertices, for a
# total of 2(q^2 + 2q + 2). For q = 13 that is 394 vertices, degree 15 or 16,
# diameter 3. The result is checked with lib.is_valid before it is used.
#
# After that, a randomized greedy step tries to add one more vertex on either
# side. It picks neighbours with spare degree that cover the same-side vertices
# within distance 2, and keeps the vertex only if lib.is_valid still holds.
# ---------------------------------------------------------------------------


def _largest_prime_power_at_most(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _pg_incidence(q):
    """PG(2, q) incidence graph: points 0..m-1, lines m..2m-1."""
    n, edges = lib.projective_plane_incidence(q)
    return n, list(edges), n // 2


def _conic_extension(q):
    """PG(2, q) plus q+1 new point-vertices (pencils on conic points) and q+1 new line-vertices (dual conic)."""
    F = lib.GF(q)
    n, edges, m = _pg_incidence(q)
    pts = lib.projective_points(q)
    idx = {v: i for i, v in enumerate(pts)}
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    centres = [idx[v] for v in conic]  # point indices; the same vectors index lines m + i

    new_edges = list(edges)
    nn = n
    for c in centres:                       # new point vertex: pencil through conic point c
        for L in adj[c]:
            new_edges.append((nn, L))
        nn += 1
    for c in centres:                       # new line vertex: all points on dual conic line m+c
        for P in adj[m + c]:
            new_edges.append((P, nn))
        nn += 1
    return nn, new_edges


def _two_colour(adj, n):
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


def _propose(n, adj, color, deg, side, d, rng):
    """Greedy neighbour set for a new vertex on `side` covering all same-side vertices within distance 2."""
    opp = [v for v in range(n) if color[v] != side and deg[v] < d]
    same = [v for v in range(n) if color[v] == side]
    if not opp or not same:
        return None
    rng.shuffle(opp)
    pool = opp
    covered = set()
    chosen = []
    while len(chosen) < d and pool:
        best_i, best_s = -1, -1
        for i, x in enumerate(pool):
            s = 0
            for w in adj[x]:
                if w not in covered:
                    s += 1
            if s > best_s:
                best_s, best_i = s, i
        if best_s <= 0:
            break
        x = pool.pop(best_i)
        chosen.append(x)
        covered.update(adj[x])
    if len(covered) < len(same):
        return None
    return chosen


def _greedy_extend(best, d, D, deadline, rng, max_misses=300):
    n, edges = best
    misses = 0
    while time_left(deadline) and misses < max_misses:
        adj = lib.adjacency(n, edges)
        color = _two_colour(adj, n)
        deg = [len(a) for a in adj]
        side = rng.randrange(2)
        chosen = _propose(n, adj, color, deg, side, d, rng)
        if chosen is None:
            misses += 1
            continue
        new_edges = edges + [(n, x) for x in chosen]
        if lib.is_valid(n + 1, new_edges, d, D):
            n, edges = n + 1, new_edges
            misses = 0
        else:
            misses += 1
    return n, edges


def time_left(deadline):
    return time.monotonic() < deadline


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)
    fallback = lib.haar_graph(d, range(d))  # K_{d,d}

    if D == 3:
        q = _largest_prime_power_at_most(d - 1)
        if q is None:
            return fallback
        n, edges, _ = _pg_incidence(q)
        best = (n, edges)
        if q + 1 == d:
            # PG(2, d-1) meets the Moore bound: nothing to extend.
            return best if lib.is_valid(n, edges, d, D) else fallback
        if not lib.is_valid(n, edges, d, D):
            return fallback
        if d - q - 1 >= 2:
            cand = _conic_extension(q)
            if lib.is_valid(cand[0], cand[1], d, D) and cand[0] > best[0]:
                best = cand
        best = _greedy_extend(best, d, D, deadline, rng)
        if lib.is_valid(best[0], best[1], d, D):
            return best
        return fallback

    # Other diameters: parent's cyclic Haar search.
    best = fallback
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
