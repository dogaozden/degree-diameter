import random
import time

import lib


def _bipartition(n, edges):
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
                elif color[v] == color[u]:
                    return None
    return color


def _augment(n, edges, d, deadline, rng):
    """Greedily add cross-side matchings between deficient vertices (keeps bipartite, diameter, degree <= d)."""
    color = _bipartition(n, edges)
    if color is None:
        return list(edges)
    edges = list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    side = [[v for v in range(n) if color[v] == 0],
            [v for v in range(n) if color[v] == 1]]
    while time.monotonic() < deadline:
        L = [u for u in side[0] if len(adj[u]) < d]
        R = [v for v in side[1] if len(adj[v]) < d]
        if not L or not R:
            break
        rng.shuffle(L)
        rng.shuffle(R)
        matchR = {}

        def try_(u, seen):
            for v in R:
                if v in seen or v in adj[u]:
                    continue
                seen.add(v)
                if v not in matchR or try_(matchR[v], seen):
                    matchR[v] = u
                    return True
            return False

        added = 0
        for u in L:
            if time.monotonic() >= deadline:
                break
            if try_(u, set()):
                added += 1
        if added == 0 or time.monotonic() >= deadline:
            break
        for v, u in matchR.items():
            adj[u].add(v)
            adj[v].add(u)
            edges.append((u, v))
    return edges


def _algebraic(d, deadline, rng):
    """D=3 constructions: AL(q) (degree q+2) and PG(2,q) (degree q+1), augmented to degree d."""
    cands = []
    for q in range(2, d + 3):
        if not lib.is_prime_power(q):
            continue
        if q + 1 <= d:
            cands.append((2 * (q * q + q + 1), "pg", q))
        if q >= 3 and q + 2 <= d:
            cands.append((2 * (q * q + q + 5), "al", q))
    cands.sort(reverse=True)
    for _, kind, q in cands:
        if time.monotonic() >= deadline:
            break
        try:
            if kind == "pg":
                n, e = lib.projective_plane_incidence(q)
            else:
                n, e = lib.araujo_lopez_graph(q)
        except Exception:
            continue
        if lib.max_degree(n, e) > d:
            continue
        e = _augment(n, e, d, deadline, rng)
        if lib.is_valid(n, e, d, 3):
            return n, e
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed)

    if D == 3:
        res = _algebraic(d, deadline, rng)
        if res is not None:
            return res

    # Safe fallback: K_{d,d} (diameter 2), then random Haar-graph search.
    best = lib.haar_graph(d, range(d))
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
    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
