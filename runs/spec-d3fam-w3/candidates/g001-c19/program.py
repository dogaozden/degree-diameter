import random
import time

import lib


def _normalize(u, v):
    return (u, v) if u < v else (v, u)


def _two_color(n, E):
    """Proper 2-colouring of the graph with edge set E (vertices 0..n-1)."""
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    return color


def _splice_search(n, edges, d, D, rng, deadline):
    """Vertex-pair splicing search.

    Pick d-1 pairwise vertex-disjoint edges (x_i in side A, y_i in side B) and remove them.
    Add two new vertices A* (side A) and B* (side B), joined to each other, with
    A* ~ y_i and B* ~ x_i for all i. Every old vertex keeps its degree, and A*, B* reach
    degree d. Accept the splice only if the diameter bound still holds, which is checked
    exactly. The graph stays bipartite by construction.
    """
    E = {_normalize(u, v) for u, v in edges}
    color = _two_color(n, E)
    best_n, best_E = n, E
    k = d - 1
    while time.monotonic() < deadline:
        elist = list(E)
        rng.shuffle(elist)
        used = set()
        chosen = []
        for u, v in elist:
            if u in used or v in used:
                continue
            if color[u] == 0:
                x, y = u, v
            else:
                x, y = v, u
            used.add(u)
            used.add(v)
            chosen.append((x, y))
            if len(chosen) == k:
                break
        if len(chosen) < k:
            continue
        A, B = n, n + 1
        E2 = set(E)
        for x, y in chosen:
            E2.discard(_normalize(x, y))
        for x, y in chosen:
            E2.add(_normalize(A, y))
            E2.add(_normalize(x, B))
        E2.add(_normalize(A, B))
        if lib.within_diameter(n + 2, list(E2), D):
            E = E2
            n += 2
            color.extend([0, 1])
            best_n, best_E = n, E
    return best_n, sorted(best_E)


def _haar_search(d, D, rng, deadline):
    """Generic fallback: random Haar graphs of growing order."""
    best = lib.haar_graph(d, range(d))  # K_{d,d}, always valid
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    search_deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    # Exact projective-plane construction (Moore-optimal) when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, edges = lib.araujo_lopez_graph(d - 2)
        except ValueError:
            n, edges = None, None
        if n is not None and lib.is_valid(n, edges, d, D):
            # Use the remaining budget to splice in extra vertex pairs.
            n2, edges2 = _splice_search(n, edges, d, D, rng, search_deadline)
            if n2 > n and lib.is_valid(n2, edges2, d, D):
                return n2, edges2
            return n, edges

    n, edges = _haar_search(d, D, rng, search_deadline)
    return n, edges
