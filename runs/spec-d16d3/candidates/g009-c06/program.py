import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases.
# ----------------------------------------------------------------------------

def _pg_prime_power(d):
    """Largest prime power q with q + 1 <= d (the projective plane PG(2, q) has degree q + 1)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _conic_arc(q, d):
    """PG(2, q) incidence plus one A-vertex per point of an arc S and one B-vertex per line of S.

    Spare capacity is s = d - q - 1 per vertex. S is the conic (plus nucleus for even q),
    and it is accepted only if every line and every point carries at most s elements of S.
    Diameter 3 is preserved by construction. The result is still checked with lib.is_valid.
    """
    s = d - q - 1
    if s < 2 or q < 3:
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    if max(cl) > s or max(cp) > s:
        return None
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        E.extend((x, m + L) for L in point_lines[P])
    for t, j in enumerate(S):
        b = 2 * m + k + t
        E.extend((Q, b) for Q in line_points[j])
    return n, E


# ----------------------------------------------------------------------------
# Reachability and growth with annealed vertex insertion.
# ----------------------------------------------------------------------------

def _reach(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        nxt = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt[v] = x
        ball = nxt
    return ball


def _bad(n, adj, D):
    """Number of unordered pairs at distance greater than D (0 means valid diameter)."""
    reach = _reach(n, adj, D)
    return sum(n - r.bit_count() for r in reach) // 2


def _colors(n, adj):
    """Two-colouring of a bipartite graph given by adjacency sets."""
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


def _grow(n, adj, d, D, deadline, rng, steps, T=0.7):
    """Repeatedly insert a new vertex whose neighbourhood covers everything within distance D.

    The initial neighbourhood is greedy set cover on radius-(D-1) balls. Remaining defects are
    repaired by annealed swaps of the new vertex's neighbours. Failed insertions are undone,
    so the graph is valid after every accepted step.
    """
    color = _colors(n, adj)
    while time.monotonic() < deadline:
        c = rng.randrange(2)
        opp = [u for u in range(n) if color[u] == 1 - c and len(adj[u]) < d]
        if not opp:
            c = 1 - c
            opp = [u for u in range(n) if color[u] == 1 - c and len(adj[u]) < d]
            if not opp:
                break
        ball = _reach(n, adj, D - 1)
        v = n
        adj.append(set())
        color.append(c)
        n += 1

        covered = 0
        pool = opp[:]
        rng.shuffle(pool)
        for _ in range(d):
            best_u, bg = -1, 0
            for u in pool:
                g = (ball[u] & ~covered).bit_count()
                if g > bg:
                    bg, best_u = g, u
            if best_u < 0:
                break
            adj[v].add(best_u)
            adj[best_u].add(v)
            covered |= ball[best_u]
            pool.remove(best_u)

        bad = _bad(n, adj, D)
        for _ in range(steps):
            if bad == 0 or time.monotonic() >= deadline:
                break
            free = [y for y in opp if y not in adj[v] and len(adj[y]) < d]
            if not free:
                break
            if len(adj[v]) < d and rng.random() < 0.5:
                y = rng.choice(free)
                adj[v].add(y)
                adj[y].add(v)
                nb = _bad(n, adj, D)
                if nb <= bad or rng.random() < math.exp(-(nb - bad) / T):
                    bad = nb
                else:
                    adj[v].discard(y)
                    adj[y].discard(v)
            elif adj[v]:
                x = rng.choice(tuple(adj[v]))
                y = rng.choice(free)
                adj[v].discard(x)
                adj[x].discard(v)
                adj[v].add(y)
                adj[y].add(v)
                nb = _bad(n, adj, D)
                if nb <= bad or rng.random() < math.exp(-(nb - bad) / T):
                    bad = nb
                else:
                    adj[v].discard(y)
                    adj[y].discard(v)
                    adj[v].add(x)
                    adj[x].add(v)

        if bad != 0:
            for u in adj[v]:
                adj[u].discard(v)
            adj.pop()
            color.pop()
            n -= 1
    return n, adj


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback[0], fallback[1]

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    seed_graph = (fallback[0], fallback[1])
    try:
        moore = lib._moore_bound(d, D)
    except Exception:
        moore = None

    if D >= 3:
        q = _pg_prime_power(d)
        if q is not None:
            n_pg, e_pg = lib.projective_plane_incidence(q)
            consider(n_pg, e_pg)
            if lib.is_valid(n_pg, e_pg, d, D):
                seed_graph = (n_pg, e_pg)
            if D == 3:
                arc = _conic_arc(q, d)
                if arc is not None:
                    consider(arc[0], arc[1])
                    if lib.is_valid(arc[0], arc[1], d, D) and arc[0] >= seed_graph[0]:
                        seed_graph = arc

    if moore is not None and best_n >= moore:
        return best_n, best_e

    # Bold stage: grow the strongest seed by annealed vertex insertion.
    try:
        n0, e0 = seed_graph
        adj = [set() for _ in range(n0)]
        for u, v in e0:
            adj[u].add(v)
            adj[v].add(u)
        n2, adj2 = _grow(n0, adj, d, D, deadline, rng, steps=150)
        e2 = [(u, w) for u in range(n2) for w in adj2[u] if u < w]
        consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback[0], list(fallback[1])
    return best_n, list(best_e)
