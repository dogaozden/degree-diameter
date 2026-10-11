import random
import time

import lib


def _colors(n, edges):
    """Two-colouring of a bipartite graph (connected components coloured independently)."""
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


def _try_insert(n, edges, d, rng, color):
    """Insert one A-vertex x and one B-vertex y (joined to each other).

    Pick a random matching of d-1 existing edges (a_i, b_i). Remove them, then
    join x to every b_i and y to every a_i. Degrees of old vertices are unchanged,
    x and y get degree d, and bipartiteness is preserved. Returns (n+2, edges) or None.
    The caller must still check diameter with lib.is_valid.
    """
    k = d - 1
    if k < 1 or len(edges) < k:
        return None
    order = list(range(len(edges)))
    rng.shuffle(order)
    used = set()
    picked = []
    for idx in order:
        u, v = edges[idx]
        if color[u] == 1:
            u, v = v, u  # u on side 0 (A), v on side 1 (B)
        if u in used or v in used:
            continue
        used.add(u)
        used.add(v)
        picked.append(idx)
        if len(picked) == k:
            break
    if len(picked) < k:
        return None
    removed = set(picked)
    x = n      # side 0 (A)
    y = n + 1  # side 1 (B)
    new_edges = [e for i, e in enumerate(edges) if i not in removed]
    for idx in picked:
        u, v = edges[idx]
        if color[u] == 1:
            u, v = v, u
        new_edges.append((u, y))
        new_edges.append((x, v))
    new_edges.append((x, y))
    return n + 2, new_edges


def _grow_by_insertion(n, edges, d, D, deadline, rng):
    """Repeatedly try to insert a vertex pair; keep only candidates that pass lib.is_valid."""
    cur_n, cur_e = n, list(edges)
    color = _colors(cur_n, cur_e)
    while time.monotonic() < deadline:
        cand = _try_insert(cur_n, cur_e, d, rng, color)
        if cand is None:
            continue
        n2, e2 = cand
        if lib.is_valid(n2, e2, d, D):
            cur_n, cur_e = n2, e2
            color = _colors(cur_n, cur_e)
    return cur_n, cur_e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D == 3:
        seed_graph = None
        if lib.is_prime_power(d - 1):
            seed_graph = lib.projective_plane_incidence(d - 1)
        elif d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                seed_graph = lib.araujo_lopez_graph(d - 2)
            except (ValueError, StopIteration, KeyError):
                seed_graph = None
        if seed_graph is not None and lib.is_valid(seed_graph[0], seed_graph[1], d, D):
            best = seed_graph
            n2, e2 = _grow_by_insertion(best[0], best[1], d, D, deadline, rng)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
