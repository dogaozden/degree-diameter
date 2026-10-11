"""Target-focused program: PG(2,q) incidence plus a conic arc extension as the base,
then annealed degree-preserving 2-switch search that adds one vertex at a time.

Every accepted graph is checked with lib.is_valid. If no improvement is found, the
program returns the best valid graph so far, so every case still returns a valid graph.
"""
import math
import random
import time

import lib


def _pg_arc_base(d):
    """Return (n, edges, colour) for PG(2,q) incidence plus a conic arc extension.

    q is the largest prime power <= d-1 and s = d-q-1 is the spare degree.
    Each arc point P adds an A-vertex on the lines through P, and each arc line j adds
    a B-vertex on the points of j. Loads stay <= s, so max degree stays <= d.
    """
    q = next((x for x in range(d - 1, 1, -1) if lib.is_prime_power(x)), None)
    if q is None:
        return None
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    s = d - q - 1
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    E = list(edges)
    col = [0] * m + [1] * m
    n = 2 * m

    S = []
    if s >= 2:
        F = lib.GF(q)
        index = {p: i for i, p in enumerate(lib.projective_points(q))}
        cand = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
        if q % 2 == 0:
            cand.append(index[(0, 1, 0)])
        cl = [0] * m
        cp = [0] * m
        for P in cand:
            for L in point_lines[P]:
                cl[L] += 1
            for Q in line_points[P]:
                cp[Q] += 1
        if max(cl) <= s and max(cp) <= s:
            S = cand

    k = len(S)
    for t, P in enumerate(S):
        x = n + t
        col.append(0)
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        y = n + k + t
        col.append(1)
        for Q in line_points[j]:
            E.append((Q, y))
    return n + 2 * k, E, col


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance more than D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _search(n, adj, col, d, D, deadline, rng):
    """Greedy fill, then annealed degree-preserving 2-switches minimising bad pairs.

    `adj` is a list of sets and is modified in place. Returns adj if bad == 0, else None.
    Every intermediate state is a valid bipartite graph with max degree <= d.
    """
    A = [v for v in range(n) if col[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if col[v] == 1 and len(adj[v]) < d]
    rng.shuffle(A)
    rng.shuffle(B)
    for a in A:
        for b in B:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) < d and b not in adj[a]:
                adj[a].add(b)
                adj[b].add(a)

    E = [(a, b) for a in range(n) if col[a] == 0 for b in adj[a]]
    cur = _bad(n, adj, D)
    if cur == 0:
        return adj
    T = 0.6
    while time.monotonic() < deadline and len(E) >= 2:
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
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
        new = _bad(n, adj, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            E[i] = (a, e)
            E[j] = (c, b)
            cur = new
            if cur == 0:
                return adj
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
        T = max(0.05, T * 0.999)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
        return fallback

    best = fallback
    best_n = fallback[0]
    best_col = [0] * d + [1] * d

    base = _pg_arc_base(d)
    if base is not None:
        n, E, col = base
        if n > best_n and lib.is_valid(n, E, d, D):
            best = (n, E)
            best_n = n
            best_col = col

    moore = lib._moore_bound(d, D)
    while best_n < moore:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        budget = remaining * 0.5

        nn = best_n + 1
        cnt0 = sum(1 for c in best_col if c == 0)
        newc = 0 if cnt0 <= best_n - cnt0 else 1
        adj = [set() for _ in range(nn)]
        for u, v in best[1]:
            adj[u].add(v)
            adj[v].add(u)
        col2 = best_col + [newc]

        res = _search(nn, adj, col2, d, D, time.monotonic() + budget, rng)
        if res is None:
            continue
        E2 = [(u, v) for u in range(nn) for v in adj[u] if u < v]
        if lib.is_valid(nn, E2, d, D):
            best = (nn, E2)
            best_n = nn
            best_col = col2

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
