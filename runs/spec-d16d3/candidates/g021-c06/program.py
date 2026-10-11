import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base construction: PG(2, q) incidence with a conic-based arc extension.
#
# For a conic C in PG(2, q) (plus the nucleus when q is even), add one
# A-vertex per point of C joined to the q+1 lines through it, and one B-vertex
# per line of C joined to the q+1 points on it. Each point and line then gains
# at most 2 extra edges, so for d = q + 3 the graph keeps max degree d and
# diameter 3.
# ----------------------------------------------------------------------------

def _conic_graph(q):
    """PG(2, q) incidence graph extended by A/B vertices for a conic (diameter 3)."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    E = list(edges)
    n = n2
    for P in S:
        x = n
        n += 1
        for L in point_lines[P]:
            E.append((x, m + L))
    for j in S:
        b = n
        n += 1
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _sides(n, edges):
    """Two-colouring of a bipartite graph (colour 0 for the first vertex in each component)."""
    adj = lib.adjacency(n, edges)
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
    return col


def _saturate(n, E, col, d, rng):
    """Add edges between deficient opposite-side vertices (keeps diameter, uses spare degree)."""
    deg = [0] * n
    for a, b in E:
        deg[a] += 1
        deg[b] += 1
    ES = set(E)
    L = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    R = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in L for b in R if (a, b) not in ES]
    rng.shuffle(pairs)
    E = list(E)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            E.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return E


# ----------------------------------------------------------------------------
# New helper: vertex insertion with degree-preserving edge-swap annealing.
#
# Insert a vertex v on a chosen side, joined to d opposite-side vertices.
# Saturated neighbours give up one random edge to make room. The resulting
# graph is then repaired by double-edge swaps (which keep every degree fixed)
# that minimise the number of vertex pairs farther apart than D.
# ----------------------------------------------------------------------------

def _insert_anneal(n, E, col, d, D, rng, deadline):
    """Try to grow the graph by one vertex; return (n+1, E, col) on success, else None."""
    c = rng.randrange(2)
    deg = [0] * n
    for a, b in E:
        deg[a] += 1
        deg[b] += 1
    pool = [x for x in range(n) if col[x] != c]
    rng.shuffle(pool)
    pool.sort(key=lambda x: deg[x] >= d)  # deficient vertices first
    chosen = pool[:d]
    if len(chosen) < d:
        return None
    E = list(E)
    full = [x for x in chosen if deg[x] >= d]
    if full:
        drop = set()
        for x in full:
            idxs = [i for i, (a, b) in enumerate(E) if (a == x or b == x) and i not in drop]
            if not idxs:
                return None
            drop.add(rng.choice(idxs))
        E = [e for i, e in enumerate(E) if i not in drop]
    v = n
    for x in chosen:
        E.append((v, x) if c == 0 else (x, v))
    ES = set(E)
    cost = lib.bad_pairs(n + 1, E, D)
    T = 2.0
    while cost > 0:
        if time.monotonic() > deadline or len(E) < 2:
            return None
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in ES or (a2, b1) in ES:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        c2 = lib.bad_pairs(n + 1, E, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            ES.discard((a1, b1))
            ES.discard((a2, b2))
            ES.add((a1, b2))
            ES.add((a2, b1))
            cost = c2
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
    return n + 1, E, col + [c]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3 and d >= 3:
        qs = [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)][:3]
        for q in qs:
            if time.monotonic() > start + 0.2 * time_limit:
                break
            consider(*_conic_graph(q))
            consider(*lib.projective_plane_incidence(q))

    if d >= 2 and time.monotonic() < deadline:
        n, E = best_n, list(best_e)
        col = _sides(n, E)
        E = _saturate(n, E, col, d, rng)
        if lib.is_valid(n, E, d, D):
            best_n, best_e = n, E
        else:
            E = list(best_e)
            col = _sides(n, E)
        while time.monotonic() < deadline:
            remaining = deadline - time.monotonic()
            slice_end = time.monotonic() + max(2.0, remaining / 4.0)
            slice_end = min(slice_end, deadline)
            res = _insert_anneal(n, E, col, d, D, rng, slice_end)
            if res is None:
                # Re-saturate with a fresh shuffle to change the starting point.
                E = _saturate(n, E, col, d, rng)
                continue
            n, E, col = res
            E = _saturate(n, E, col, d, rng)
            if n > best_n and lib.is_valid(n, E, d, D):
                best_n, best_e = n, list(E)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
