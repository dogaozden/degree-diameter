import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane and generalized quadrangle bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving growth).
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


def _extend_cover(n, edges, d, D, deadline, rng, always_random=False, max_add=10 ** 9):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the graph."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    added_count = 0

    while time.monotonic() < deadline and added_count < max_add:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, always_random or attempt > 0)
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
                added_count += 1
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
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
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, always_random=False):
    """Extend by cover vertices first, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, always_random)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW: degree-constrained edge annealing that repairs diameter.
#
# State: a bipartite graph on a fixed vertex set with max degree d.
# Move: pick a random non-adjacent opposite pair (a, b). Make room by deleting
# one random edge at each full endpoint, add (a, b), and accept by Metropolis
# on the number of vertex pairs at distance > D. Bipartiteness and degree
# bounds are preserved by construction, so only the diameter is checked.
# ----------------------------------------------------------------------------

def _bad_pairs_sets(n, nb, D):
    """Number of unordered pairs at distance > D, from neighbour sets."""
    adj = [list(s) for s in nb]
    balls = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in balls) // 2


def _anneal_fix(n, edges, d, D, color, deadline, rng):
    """Anneal edges until every pair is within D; returns the edge list or None."""
    nb = [set() for _ in range(n)]
    for u, v in edges:
        nb[u].add(v)
        nb[v].add(u)
    A = [v for v in range(n) if color[v] == 0]
    B = [v for v in range(n) if color[v] == 1]
    if not A or not B:
        return None
    cost = _bad_pairs_sets(n, nb, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cost > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - start) / span
        T = 0.5 * (0.02 ** frac)
        a = rng.choice(A)
        b = rng.choice(B)
        if b in nb[a]:
            continue
        rem = []
        if len(nb[a]) >= d:
            x = rng.choice(list(nb[a]))
            nb[a].discard(x)
            nb[x].discard(a)
            rem.append((a, x))
        if len(nb[b]) >= d:
            y = rng.choice(list(nb[b]))
            nb[b].discard(y)
            nb[y].discard(b)
            rem.append((y, b))
        nb[a].add(b)
        nb[b].add(a)
        c2 = _bad_pairs_sets(n, nb, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            nb[a].discard(b)
            nb[b].discard(a)
            for u, v in rem:
                nb[u].add(v)
                nb[v].add(u)
    if cost > 0:
        return None
    return [(u, v) for u in range(n) for v in nb[u] if u < v]


def _improve(n, edges, d, D, deadline, rng, consider_fn):
    """Repeatedly add one cover vertex, saturate, then anneal to repair diameter."""
    while time.monotonic() < deadline:
        n2, e2 = _extend_cover(n, edges, d, D, deadline, rng, True, max_add=1)
        if n2 == n:
            break
        e2 = _saturate_edges(n2, e2, d, rng)
        adj = [[] for _ in range(n2)]
        for u, v in e2:
            adj[u].append(v)
            adj[v].append(u)
        color = _bipartition(n2, adj)
        budget_end = min(deadline, time.monotonic() + 8.0)
        res = _anneal_fix(n2, e2, d, D, color, budget_end, rng)
        if res is not None:
            n, edges = n2, res
            consider_fn(n, edges)
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.85 * time_limit
    deadline = start + total
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

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.3 * total, rng)
            consider(n2, e2)
        return best

    if D >= 4 and d >= 3:
        # Generalized quadrangle bases for the two largest usable prime powers.
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q) and q <= 7][:2]
        grown_bases = []
        for q in qs:
            if time.monotonic() >= start + 0.3 * total:
                break
            gn, ge = _gq_w(q)
            consider(gn, ge)
            gn2, ge2 = _grow(gn, ge, d, D, start + 0.3 * total, rng)
            consider(gn2, ge2)
            grown_bases.append((gn2, ge2))
            if time.monotonic() >= start + 0.3 * total:
                break

        # Pick the largest valid starting point and grow it with annealed repair.
        if grown_bases:
            cn, ce = max(grown_bases, key=lambda t: t[0])
            if cn >= best_n and lib.is_valid(cn, ce, d, D):
                _improve(cn, ce, d, D, deadline, rng, consider)
            else:
                _improve(best_n, best[1], d, D, deadline, rng, consider)
        else:
            _improve(best_n, best[1], d, D, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
