"""Diameter-3 bipartite search for (d, D) with a safe fallback.

Pipeline:
  1. Safe fallback K_{d,d} (valid for D >= 2).
  2. For D = 3: PG(2,q) incidence with q the largest prime power with q+1 <= d,
     then the conic arc extension (record-type construction), each checked with lib.is_valid.
  3. Insertion search: add one vertex at a time, saturate spare degree, and repair
     distance violations with simulated-annealing edge switches. Only states that pass
     lib.is_valid are kept.

Note: for d = 16, D = 3 the arc/pencil family is capped at 394 when q = 13 (a set with at
most two points per line in PG(2,13) has at most 14 points). Beating 394 needs the search
step to find configurations outside that family, which is not guaranteed.
"""
import math
import random
import time

import lib


def _moore3(d):
    """Moore-type ceiling for bipartite graphs with max degree d and diameter 3."""
    return 2 * (1 + (d - 1) + (d - 1) ** 2)


def _best_q(d):
    """Largest prime power q with q + 1 <= d (q >= 2), or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency collections."""
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


def _pg_arc_graph(q):
    """PG(2,q) incidence plus a new A-vertex per conic point and a new B-vertex per conic line.

    Points are 0..m-1 (colour 0), lines m..2m-1 (colour 1). Returns (n, edges).
    """
    m2, pedges = lib.projective_plane_incidence(q)
    m = m2 // 2
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in pedges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    k = len(S)
    n = 2 * m + 2 * k
    E = list(pedges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _reach_bad(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (unreachable pairs count)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt[v] = r
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _saturate(n, adj, color, d, rng):
    """Add edges between opposite-colour vertices with spare degree. Never increases distances."""
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _search(n, adj, color, d, D, deadline, rng, on_valid):
    """Insert vertices one at a time; repair with annealed edge switches.

    adj and color are lists updated in place. on_valid(n, adj) is called after each success.
    A failed insertion is rolled back, so every reported state is a repaired one.
    """
    while time.monotonic() < deadline:
        snap_adj = [set(a) for a in adj]
        snap_color = list(color)
        snap_n = n

        c = rng.randrange(2)
        adj.append(set())
        color.append(c)
        n += 1
        v = n - 1
        cands = [u for u in range(v) if color[u] != c and len(adj[u]) < d]
        rng.shuffle(cands)
        for u in cands[:d]:
            adj[v].add(u)
            adj[u].add(v)

        bad = _reach_bad(n, adj, D)
        iters = 200
        for it in range(iters):
            if bad == 0 or time.monotonic() >= deadline:
                break
            T = 1.5 * (0.1 ** (it / iters))
            a = rng.randrange(n)
            if not adj[a]:
                continue
            b = rng.choice(list(adj[a]))
            x = None
            for _ in range(30):
                y = rng.randrange(n)
                if color[y] != color[a] and y != b and y not in adj[a] and len(adj[y]) < d:
                    x = y
                    break
            if x is None:
                continue
            adj[a].discard(b)
            adj[b].discard(a)
            adj[a].add(x)
            adj[x].add(a)
            nb = _reach_bad(n, adj, D)
            delta = nb - bad
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                bad = nb
            else:
                adj[a].discard(x)
                adj[x].discard(a)
                adj[a].add(b)
                adj[b].add(a)

        if bad == 0:
            _saturate(n, adj, color, d, rng)
            on_valid(n, adj)
        else:
            adj[:] = snap_adj
            color[:] = snap_color
            n = snap_n
    return n


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best_n, best_e = fallback

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    ceiling = _moore3(d) if D == 3 else None

    if D == 3:
        q = _best_q(d)
        if q is not None:
            m2, pe = lib.projective_plane_incidence(q)
            consider(m2, pe)
            n_a, e_a = _pg_arc_graph(q)
            consider(n_a, e_a)

    if ceiling is not None and best_n >= ceiling:
        return best_n, best_e

    adj = [set() for _ in range(best_n)]
    for u, v in best_e:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(best_n, adj)

    def on_valid(n, adj_):
        nonlocal best_n, best_e
        if n > best_n:
            E = [(u, v) for u in range(n) for v in adj_[u] if u < v]
            if lib.is_valid(n, E, d, D):
                best_n, best_e = n, E

    _search(best_n, adj, color, d, D, deadline, rng, on_valid)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, best_e
