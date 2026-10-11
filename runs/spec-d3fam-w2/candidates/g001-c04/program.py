import math
import random
import time

import lib


def _sides(n, adj):
    """2-colour a bipartite graph given as adjacency sets. Returns a colour list (0 or 1) per vertex."""
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
    return [c if c != -1 else 0 for c in color]


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance more than D, via bitmask balls."""
    nbl = [list(s) for s in adj]
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nbl[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _extend(n0, edges0, d, D, deadline, rng):
    """Try to build a valid d-regular-on-new-vertices graph with n0 + 2 vertices.

    Step 1: attach two new vertices x (side A) and y (side B) by 2-switch-like moves
            (a,b) -> (x,b),(a,y), which keep every old degree unchanged.
    Step 2: simulated annealing over bipartite 2-switches, minimising the number of
            pairs at distance > D. Degrees are preserved, so max degree stays <= d.
    Returns (N, edges) only if the cost reaches 0, otherwise None.
    """
    adj = [set() for _ in range(n0)]
    for u, v in edges0:
        adj[u].add(v)
        adj[v].add(u)
    color = _sides(n0, adj)
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges0]

    x, y = n0, n0 + 1
    adj.append(set())
    adj.append(set())
    N = n0 + 2

    tries = 0
    while len(adj[x]) < d and tries < 200000 and time.monotonic() < deadline:
        tries += 1
        i = rng.randrange(len(E))
        a, b = E[i]
        if a >= n0 or b >= n0:
            continue
        if b in adj[x] or a in adj[y]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[x].add(b)
        adj[b].add(x)
        adj[a].add(y)
        adj[y].add(a)
        E[i] = (x, b)
        E.append((a, y))
    if len(adj[x]) < d or len(adj[y]) < d:
        return None

    M = len(E)
    cur = _bad_pairs(N, adj, D)
    t_start = time.monotonic()
    span = max(deadline - t_start, 1e-6)
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(M)
        j = rng.randrange(M)
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _bad_pairs(N, adj, D)
        delta = new - cur
        frac = (time.monotonic() - t_start) / span
        T = 0.5 * (1.0 - frac) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            E[i] = (a, e)
            E[j] = (c, b)
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    if cur != 0:
        return None
    return N, [(a, b) for a, b in E]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.0, min(0.8 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)
    q = d - 1

    # Optimal D = 3 graph when d - 1 is a prime power.
    if D == 3 and lib.is_prime_power(q):
        n, edges = lib.projective_plane_incidence(q)
        if lib.is_valid(n, edges, d, D):
            return n, edges

    # D = 3 with d - 2 a prime power: Araujo-Pardo & Lopez record graph, then a
    # simulated-annealing attempt to add two more vertices while keeping diameter 3.
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n0, edges0 = lib.araujo_lopez_graph(d - 2)
        except Exception:
            n0, edges0 = None, None
        if n0 is not None and lib.is_valid(n0, edges0, d, D):
            base = (n0, edges0)
            try:
                res = _extend(n0, edges0, d, D, deadline, rng)
            except Exception:
                res = None
            if res is not None and lib.is_valid(res[0], res[1], d, D):
                return res
            return base

    # Generic fallback: cyclic Haar graph search (valid for any d, D).
    best = lib.haar_graph(d, range(d))  # K_{d,d}
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
    if lib.is_valid(best[0], best[1], d, D):
        return best
    return lib.haar_graph(d, range(d))
