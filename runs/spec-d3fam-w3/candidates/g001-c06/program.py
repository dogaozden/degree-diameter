import random
import time

import lib


def _colors(n, edges):
    """Return (color, adj) for a bipartite graph: color[v] in {0, 1}."""
    adj = lib.adjacency(n, edges)
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
    return color, adj


def _extend(n, edges, d, D, deadline, rng):
    """Try to add (point, line) vertex pairs wired to spare-degree vertices.

    Every candidate is checked with lib.is_valid, so the returned graph is always valid.
    Returns the best valid (n, edges) found; the input is returned if nothing works.
    """
    while time.monotonic() < deadline:
        color, adj = _colors(n, edges)
        spare = [[v for v in range(n) if color[v] == c and len(adj[v]) < d] for c in (0, 1)]
        if not spare[0] or not spare[1]:
            break
        p, l = n, n + 1  # p gets color 0 (point side), l gets color 1 (line side)
        cap1 = min(d - 1, len(spare[1]))
        cap0 = min(d - 1, len(spare[0]))
        if rng.random() < 0.5:
            k1, k2 = cap1, cap0
        else:
            k1, k2 = rng.randint(1, cap1), rng.randint(1, cap0)
        nb_lines = rng.sample(spare[1], k1)
        nb_pts = rng.sample(spare[0], k2)
        cand = list(edges)
        cand.append((p, l))
        cand.extend((p, x) for x in nb_lines)
        cand.extend((l, y) for y in nb_pts)
        if lib.is_valid(n + 2, cand, d, D):
            n, edges = n + 2, cand
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    # Bold path: Araujo-Pardo & Lopez construction on PG(2, q), q = d - 2, for D = 3.
    q = d - 2
    if D == 3 and q >= 3 and lib.is_prime_power(q):
        try:
            n, edges = lib.araujo_lopez_graph(q)
        except Exception:
            n, edges = None, None
        if n is not None and lib.is_valid(n, edges, d, D):
            return _extend(n, edges, d, D, deadline, rng)

    # Safe fallback: the parent's approach.
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    fallback_deadline = start + 0.8 * time_limit
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
    m, misses = d + 1, 0
    while time.monotonic() < fallback_deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= fallback_deadline:
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
