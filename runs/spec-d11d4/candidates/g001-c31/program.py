"""Pair insertion with verified diameter, on top of generalized quadrangle and projective plane bases.

New routine (_pair_insert): from a base bipartite graph whose vertices have spare degree, repeatedly
attach a new adjacent pair (x, y) with x on side c and y on the other side. x takes d-1 spare
neighbours on side 1-c, and y takes d-1 spare neighbours on side c. Both new vertices get degree d.
Neighbour sets are chosen by greedy ball-cover (radius 3 balls in the current graph). Acceptance is
decided by an exact BFS from x and from y to depth D. Adding vertices and edges never lengthens an
existing distance, so the old pairs stay within D, and the BFS from the two new vertices covers
every new pair. Each accepted pair adds 2 vertices.
"""
import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases.
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (q <= 9 for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Graph helpers.
# ----------------------------------------------------------------------------

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


def _greedy_pick(pool, ball, k, rng, randomize):
    """Greedily pick k distinct vertices from pool maximising new coverage of their radius-r balls."""
    pool = list(pool)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    for _ in range(k):
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        bg = max(gains)
        if randomize and rng.random() < 0.3:
            opts = [i for i, g in enumerate(gains) if g >= bg - 1]
            i = rng.choice(opts)
        else:
            i = gains.index(bg)
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen


def _reaches_all(adj, src, D, N):
    """True if every one of the N vertices is within distance D of src."""
    seen = [False] * N
    seen[src] = True
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = True
                    nxt.append(v)
        cnt += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return cnt == N


def _try_attach(adj, side, n, T, U, c, D):
    """Temporarily attach pair x=n (side c, adjacent to T and y) and y=n+1 (side 1-c, adjacent to U).

    Keeps the attachment if both x and y reach everything within D; otherwise rolls back.
    """
    x, y = n, n + 1
    adj.append([])
    adj.append([])
    side.append(c)
    side.append(1 - c)
    for t in T:
        adj[t].append(x)
        adj[x].append(t)
    for u in U:
        adj[u].append(y)
        adj[y].append(u)
    adj[x].append(y)
    adj[y].append(x)
    ok = _reaches_all(adj, x, D, n + 2) and _reaches_all(adj, y, D, n + 2)
    if not ok:
        for t in T:
            adj[t].pop()
        for u in U:
            adj[u].pop()
        adj.pop()
        adj.pop()
        side.pop()
        side.pop()
    return ok


def _pair_insert(n0, edges0, d, D, rng, deadline):
    """Repeatedly attach verified adjacent pairs (x, y) using spare degree. Returns (n, edges)."""
    k = d - 1
    n = n0
    edges = list(edges0)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    side = _bipartition(n, adj)
    if k < 1:
        return n, edges
    ball3 = None
    fails = 0
    while time.monotonic() < deadline and fails < 60:
        if ball3 is None:
            ball3 = _balls_radius(n, adj, 3)
        cs = [0, 1]
        rng.shuffle(cs)
        chosen_c = None
        spT = spU = None
        for c in cs:
            spT = [v for v in range(n) if side[v] == 1 - c and len(adj[v]) < d]
            spU = [v for v in range(n) if side[v] == c and len(adj[v]) < d]
            if len(spT) >= k and len(spU) >= k:
                chosen_c = c
                break
        if chosen_c is None:
            break
        c = chosen_c
        ok = False
        T = U = None
        for att in range(8):
            if time.monotonic() >= deadline:
                break
            T = _greedy_pick(spT, ball3, k, rng, att > 0)
            U = _greedy_pick(spU, ball3, k, rng, att > 0)
            if _try_attach(adj, side, n, T, U, c, D):
                ok = True
                break
        if ok:
            x, y = n, n + 1
            for t in T:
                edges.append((t, x))
            for u in U:
                edges.append((u, y))
            edges.append((x, y))
            n += 2
            ball3 = None
            fails = 0
        else:
            fails += 1
    return n, edges


# ----------------------------------------------------------------------------
# Entry point.
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
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    base = None
    if D == 3:
        base = _best_pg(d)
    elif D == 4:
        base = _best_gq(d)

    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        n2, e2 = _pair_insert(n0, e0, d, D, rng, deadline)
        consider(n2, e2)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
