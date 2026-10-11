import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Helpers.
# ----------------------------------------------------------------------------

def _bad_count(n, adj, D):
    """Ordered count of vertex pairs at distance > D (bitmask BFS over adjacency lists/sets)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


# ----------------------------------------------------------------------------
# Base constructions for D = 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _ara(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2, q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Growth by spare-degree use (cover extension + saturation); keeps diameter <= D.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover all vertices within distance D-1."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(100):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (only adds edges)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Augmentation by two vertices (point P and line L) via degree-preserving 2-switches.
# ----------------------------------------------------------------------------

def _augment(n, edges, d, D, rng, deadline):
    """Add two new vertices P (colour 1) and L (colour 0) keeping all old degrees.

    Step 1: pick a matching of d edges (a_i, b_i); replace each by (a_i, P) and (b_i, L).
    Step 2: anneal with 2-switches (a,b),(c,e) -> (a,e),(c,b), which keep degrees and
            bipartiteness, minimising the number of pairs at distance > D.
    Returns (n+2, edges) with diameter <= D, or None if the search fails before the deadline.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _bipartition(n, [list(s) for s in adj])

    P, L = n, n + 1
    adj.append(set())
    adj.append(set())
    N = n + 2

    oriented = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]
    rng.shuffle(oriented)
    used, pick = set(), []
    for idx, (a, b) in enumerate(oriented):
        if a not in used and b not in used:
            pick.append(idx)
            used.add(a)
            used.add(b)
            if len(pick) == d:
                break
    if len(pick) < d:
        return None

    picked = set(pick)
    E = [oriented[i] for i in range(len(oriented)) if i not in picked]
    for idx in pick:
        a, b = oriented[idx]
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(P)
        adj[P].add(a)
        adj[b].add(L)
        adj[L].add(b)
        E.append((a, P))
        E.append((L, b))

    M = len(E)
    cur = _bad_count(N, adj, D)
    it = 0
    iters_scale = 4000
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        it += 1
        T = 1.0 * (0.05 ** min(1.0, (it % iters_scale) / iters_scale))
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new = _bad_count(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return N, list(E)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # 1. Structured bases for D = 3: Araujo-Pardo-Lopez record, else plain PG incidence.
    if D == 3:
        ara = _ara(d)
        if ara is not None:
            consider(ara[0], ara[1])
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # 2. Use spare degree of the base graph.
    gn, ge = _grow(best_n, best[1], d, D, start + 0.25 * time_limit, rng)
    if gn > best_n and lib.is_valid(gn, ge, d, D):
        consider(gn, ge)

    # 3. Repeated two-vertex augmentation with annealing, interleaved with spare-degree growth.
    cur = best
    fails = 0
    slice_len = max(1.0, 0.12 * time_limit)
    while time.monotonic() < deadline and fails < 60:
        if cur[0] + 2 > _moore(d, D):
            break
        slice_end = min(deadline, time.monotonic() + slice_len)
        res = _augment(cur[0], cur[1], d, D, rng, slice_end)
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            cur = res
            fails = 0
            g_end = min(deadline, time.monotonic() + 0.5 * slice_len)
            gn, ge = _grow(cur[0], cur[1], d, D, g_end, rng)
            if gn >= cur[0] and lib.is_valid(gn, ge, d, D):
                cur = (gn, ge)
            consider(cur[0], cur[1])
        else:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
