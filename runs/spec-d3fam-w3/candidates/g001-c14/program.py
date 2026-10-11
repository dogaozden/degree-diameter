import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Known constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _ara(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Generic helpers.
# ----------------------------------------------------------------------------

def _prime_powers_upto(x):
    return [q for q in range(2, x + 1) if lib.is_prime_power(q)]


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


def _extend_cover(n, edges, d, D, deadline, rng):
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

    while time.monotonic() < deadline:
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


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices first, then saturate edges with the leftover spare degree."""
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
# NEW construction: pencil-cover growth of a projective plane (diameter 3).
#
# Start from PG(2, q), whose vertices have degree q+1. If d >= q+2, every
# vertex has spare degree. A new point-side vertex x is joined to a set T of
# lines that covers every point (a full pencil of q+1 lines through one point
# is the canonical choice). Then x reaches every point within 2 and every line
# within 3, using a point of T as the middle vertex. Symmetrically, a new
# line-side vertex y is joined to a set U of points covering every line.
# Pendant additions are accepted only if the whole graph stays at diameter 3,
# checked exactly with lib.bad_pairs. Rejected additions are rolled back.
# ----------------------------------------------------------------------------

def _cover_pick(targets, cands, adj, d, rng):
    """Greedy choice of at most d candidates whose neighbourhoods cover `targets`; None if impossible."""
    need = set(targets)
    pool = list(cands)
    rng.shuffle(pool)
    chosen = []
    while need and len(chosen) < d and pool:
        best_t = None
        best_g = 0
        for t in pool:
            g = 0
            for w in adj[t]:
                if w in need:
                    g += 1
            if g > best_g:
                best_g = g
                best_t = t
        if best_t is None:
            break
        chosen.append(best_t)
        pool.remove(best_t)
        need.difference_update(adj[best_t])
    return chosen if not need else None


def _pencil_grow(n, edges, d, rng, deadline):
    """Repeatedly add a cover-joined vertex on either side while diameter 3 is preserved."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    deg = [len(a) for a in adj]
    fails = 0
    while time.monotonic() < deadline and fails < 40:
        c = rng.randrange(2)
        targets = [v for v in range(n) if color[v] == c]
        cands = [v for v in range(n) if color[v] != c and deg[v] < d]
        T = _cover_pick(targets, cands, adj, d, rng)
        if not T:
            fails += 1
            continue
        v = n
        adj.append(list(T))
        deg.append(len(T))
        color.append(c)
        for t in T:
            adj[t].append(v)
            deg[t] += 1
            edges.append((t, v))
        n += 1
        if max(deg) <= d and lib.bad_pairs(n, edges, 3) == 0:
            fails = 0
        else:
            # Roll back the tentative vertex (LIFO order keeps this exact).
            n -= 1
            for t in T:
                adj[t].pop()
                deg[t] -= 1
                edges.pop()
            adj.pop()
            deg.pop()
            color.pop()
            fails += 1
    return n, edges


# ----------------------------------------------------------------------------
# Degree-preserving 2-switch annealing on bipartite graphs (diameter 3).
# ----------------------------------------------------------------------------

def _swap_search(d, M, rng, deadline):
    """Anneal a d-regular bipartite graph on M+M vertices to diameter 3; return edge list or None."""
    N = 2 * M
    adj = [[] for _ in range(N)]
    E = []
    for i in range(M):
        for s in range(d):
            b = M + (i + s) % M
            E.append((i, b))
            adj[i].append(b)
            adj[b].append(i)
    has = set(E)

    def set_edge(k, new):
        a, b = E[k]
        adj[a].remove(b)
        adj[b].remove(a)
        has.discard((a, b))
        a2, b2 = new
        adj[a2].append(b2)
        adj[b2].append(a2)
        has.add(new)
        E[k] = new

    def cost():
        reach = [1 << v for v in range(N)]
        for _ in range(3):
            nxt = []
            for v in range(N):
                r = reach[v]
                for u in adj[v]:
                    r |= reach[u]
                nxt.append(r)
            reach = nxt
        return sum(N - r.bit_count() for r in reach) // 2

    def try_switch(i, j):
        if i == j:
            return None
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            return None
        if (a1, b2) in has or (a2, b1) in has:
            return None
        return a1, b1, a2, b2

    for _ in range(5 * len(E)):
        if time.monotonic() >= deadline:
            return None
        res = try_switch(rng.randrange(len(E)), rng.randrange(len(E)))
        if res is None:
            continue
        a1, b1, a2, b2 = res
        i = E.index((a1, b1))
        j = E.index((a2, b2))
        set_edge(i, (a1, b2))
        set_edge(j, (a2, b1))

    cur = cost()
    T0 = 1.5
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - start) / span
        T = T0 * (0.01 ** frac)
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        res = try_switch(i, j)
        if res is None:
            continue
        a1, b1, a2, b2 = res
        set_edge(i, (a1, b2))
        set_edge(j, (a2, b1))
        new = cost()
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            set_edge(i, (a1, b1))
            set_edge(j, (a2, b2))
    if cur == 0:
        return list(E)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
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
        ara = _ara(d)
        if ara is not None:
            consider(ara[0], ara[1])

        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # NEW: pencil-cover growth from PG(2, q) for the two largest prime powers q with q + 1 <= d.
        cands_q = [q for q in _prime_powers_upto(d - 1) if q + 1 <= d][-2:]
        for idx, q in enumerate(cands_q):
            t_end = start + (0.15 + 0.15 * idx) * time_limit
            n0, e0 = lib.projective_plane_incidence(q)
            n1, e1 = _pencil_grow(n0, e0, d, random.Random(seed * 131 + q), min(t_end, deadline))
            consider(n1, e1)

        n2, e2 = _grow(best_n, best[1], d, D, start + 0.5 * time_limit, rng)
        consider(n2, e2)

        # Remaining time: 2-switch annealing for larger regular bipartite graphs.
        M = best_n // 2 + 1
        while time.monotonic() < deadline:
            E = _swap_search(d, M, rng, deadline)
            if E is None:
                break
            consider(2 * M, [(a, b) for a, b in E])
            M += 1
    else:
        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
                n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.35 * time_limit, rng)
                consider(n2, e2)
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.6 * time_limit, rng)
                consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
