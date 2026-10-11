import random
import time

import lib


# ----------------------------------------------------------------------------
# Adjacency-set helpers. Every graph is kept as (n, adj, color) where
# adj[v] is a set of neighbours and color[v] in {0, 1} is the bipartition side.
# ----------------------------------------------------------------------------

def _balls(n, adj, R):
    """Bitmask of all vertices within distance R of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _valid(n, adj, d, D):
    """Degree <= d and every pair within distance D (bipartiteness is kept by construction)."""
    if any(len(a) > d for a in adj):
        return False
    full = (1 << n) - 1
    return all(r == full for r in _balls(n, adj, D))


def _to_edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _complete_bipartite(d):
    """K_{d,d}: diameter 2, degree d, always valid for D >= 2."""
    n = 2 * d
    adj = [set() for _ in range(n)]
    for a in range(d):
        for b in range(d, 2 * d):
            adj[a].add(b)
            adj[b].add(a)
    color = [0] * d + [1] * d
    return n, adj, color


# ----------------------------------------------------------------------------
# Baseline: PG(2,q) incidence with spare-capacity arc extension (diameter 3).
# Chooses the largest valid result over prime powers q with q + 1 <= d.
# ----------------------------------------------------------------------------

def _arc_base(d, rng, deadline):
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
        n2, E = lib.projective_plane_incidence(q)
        m = n2 // 2
        pl = [[] for _ in range(m)]   # point -> lines (line indices)
        lp = [[] for _ in range(m)]   # line -> points
        for u, v in E:
            pl[u].append(v - m)
            lp[v - m].append(u)
        s = d - q - 1
        S = []
        if s >= 1:
            order = list(range(m))
            for _ in range(40):
                if time.monotonic() > deadline:
                    break
                rng.shuffle(order)
                cl = [0] * m
                cp = [0] * m
                T = []
                for P in order:
                    if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                        T.append(P)
                        for L in pl[P]:
                            cl[L] += 1
                        for Q in lp[P]:
                            cp[Q] += 1
                if len(T) > len(S):
                    S = T
        k = len(S)
        n = 2 * m + 2 * k
        adj = [set() for _ in range(n)]
        color = [0] * m + [1] * m + [0] * k + [1] * k
        for u, v in E:
            adj[u].add(v)
            adj[v].add(u)
        for t, P in enumerate(S):          # A-vertex on the lines through P
            x = 2 * m + t
            for L in pl[P]:
                adj[x].add(m + L)
                adj[m + L].add(x)
        for t, j in enumerate(S):          # B-vertex on the points of line j
            b = 2 * m + k + t
            for Q in lp[j]:
                adj[Q].add(b)
                adj[b].add(Q)
        if _valid(n, adj, d, 3) and (best is None or n > best[0]):
            best = (n, adj, color)
    return best


# ----------------------------------------------------------------------------
# Bold search: grow the graph by inserting new vertices whose neighbourhoods
# cover all old vertices within radius D-1. When a chosen neighbour is full,
# one of its edges is evicted to free a slot. Insertions are accepted only if
# the whole graph stays valid. Spare cross edges are added when no insertion
# is found (adding edges never breaks validity).
# ----------------------------------------------------------------------------

def _grow(n, adj, color, d, D, rng, deadline):
    best = (n, [set(a) for a in adj])
    cur_n, cur_adj, cur_col = n, [set(a) for a in adj], list(color)
    R = D - 1
    while time.monotonic() < deadline:
        side = rng.randrange(2)
        balls = _balls(cur_n, cur_adj, R)
        full = (1 << cur_n) - 1
        pool = [u for u in range(cur_n) if cur_col[u] == 1 - side]
        rng.shuffle(pool)
        covered = 0
        chosen = []
        while covered != full and len(chosen) < d and pool:
            bi, bg = -1, 0
            for i, u in enumerate(pool):
                g = (balls[u] & ~covered).bit_count()
                # prefer candidates with free capacity (small bonus, not a hard rule)
                if len(cur_adj[u]) < d:
                    g = g * 2 + 1
                if g > bg:
                    bg, bi = g, i
            if bi < 0:
                break
            u = pool.pop(bi)
            chosen.append(u)
            covered |= balls[u]

        if covered == full:
            A = [set(a) for a in cur_adj]
            C = list(cur_col)
            N = cur_n
            for u in chosen:
                if len(A[u]) >= d:
                    x = rng.choice(sorted(A[u]))
                    A[u].discard(x)
                    A[x].discard(u)
            w = N
            A.append(set())
            C.append(side)
            for u in chosen:
                A[u].add(w)
                A[w].add(u)
            if _valid(N + 1, A, d, D):
                cur_n, cur_adj, cur_col = N + 1, A, C
                if cur_n > best[0]:
                    best = (cur_n, [set(a) for a in A])
                continue

        # Perturbation: add a spare cross edge (valid, keeps bipartiteness).
        spare_a = [u for u in range(cur_n) if len(cur_adj[u]) < d and cur_col[u] == 0]
        spare_b = [u for u in range(cur_n) if len(cur_adj[u]) < d and cur_col[u] == 1]
        if spare_a and spare_b:
            for _ in range(20):
                u = rng.choice(spare_a)
                v = rng.choice(spare_b)
                if v not in cur_adj[u]:
                    cur_adj[u].add(v)
                    cur_adj[v].add(u)
                    break
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback, valid for D >= 2.
    fb_n, fb_adj, fb_col = _complete_bipartite(d)
    fallback = (fb_n, _to_edges(fb_n, fb_adj))
    best = fallback

    # Starting point: arc-extended projective plane when D >= 3, else K_{d,d}.
    start_graph = None
    if D >= 3:
        start_graph = _arc_base(d, rng, start + 0.10 * time_limit)
    if start_graph is None:
        start_graph = (fb_n, fb_adj, fb_col)

    n0, adj0, col0 = start_graph
    best_n, best_adj = _grow(n0, adj0, col0, d, D, rng, start + 0.85 * time_limit)
    cand = (best_n, _to_edges(best_n, best_adj))
    if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
        best = cand

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
