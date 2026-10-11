import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
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
# Adjacency helpers (sets per vertex, with an undo log).
# ----------------------------------------------------------------------------

def _two_colour(n, adj_lists):
    """Two-colouring of a bipartite graph given by adjacency lists."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj_lists[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _add(adj, ops, a, b):
    adj[a].add(b)
    adj[b].add(a)
    ops.append((1, a, b))


def _rem(adj, ops, a, b):
    adj[a].discard(b)
    adj[b].discard(a)
    ops.append((0, a, b))


def _undo(adj, ops):
    for kind, a, b in reversed(ops):
        if kind:
            adj[a].discard(b)
            adj[b].discard(a)
        else:
            adj[a].add(b)
            adj[b].add(a)
    ops.clear()


def _edges_of(n, adj, side):
    return [(a, b) for a in range(n) if side[a] == 0 for b in adj[a]]


def _bad_count(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (bitmask BFS)."""
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


# ----------------------------------------------------------------------------
# Deficiency-driven annealing with degree-preserving and degree-shifting moves.
#
# Idea ("transfer annealing"): a valid graph G is extended by one new vertex
# per side. The new vertices start deficient. Moves are:
#   * 2-switch: (a,b),(c,e) -> (a,e),(c,b), which keeps every degree.
#   * transfer: move one endpoint of an edge (z,y) to a deficient vertex x on
#     the same side as z, which lowers the deficiency of x and raises z's.
#   * rewire: delete an edge, which frees two degree slots.
# After each move, every pair of deficient opposite-side vertices that is not
# yet adjacent is joined greedily. Adding edges never increases a distance, so
# the greedy fill is always safe. The cost is the number of pairs at distance
# greater than D. The Metropolis rule is applied to that cost, and failed moves
# are undone through a log.
# ----------------------------------------------------------------------------

def _fill(adj, ops, side, n, d, rng):
    A = [v for v in range(n) if side[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
    rng.shuffle(A)
    rng.shuffle(B)
    for a in A:
        if len(adj[a]) >= d:
            continue
        for b in B:
            if len(adj[b]) < d and b not in adj[a]:
                _add(adj, ops, a, b)
                if len(adj[a]) >= d:
                    break


def _two_switch(adj, ops, A, rng):
    a = rng.choice(A)
    if not adj[a]:
        return
    b = rng.choice(list(adj[a]))
    c = rng.choice(A)
    if c == a or not adj[c]:
        return
    e = rng.choice(list(adj[c]))
    if e in adj[a] or b in adj[c]:
        return
    _rem(adj, ops, a, b)
    _rem(adj, ops, c, e)
    _add(adj, ops, a, e)
    _add(adj, ops, c, b)


def _transfer(adj, ops, A, B, d, rng):
    if rng.random() < 0.5:
        X, Y = A, B
    else:
        X, Y = B, A
    defX = [v for v in X if len(adj[v]) < d]
    if not defX:
        return
    x = rng.choice(defX)
    y = rng.choice(Y)
    if y in adj[x] or not adj[y]:
        return
    z = rng.choice(list(adj[y]))
    _rem(adj, ops, z, y)
    _add(adj, ops, x, y)


def _rewire(adj, ops, A, rng):
    a = rng.choice(A)
    if adj[a]:
        b = rng.choice(list(adj[a]))
        _rem(adj, ops, a, b)


def _anneal(n, adj, side, d, D, rng, deadline):
    """Anneal until the bad-pair count is zero or the deadline passes. Returns True on success."""
    A = [v for v in range(n) if side[v] == 0]
    B = [v for v in range(n) if side[v] == 1]
    ops = []
    cost = _bad_count(n, adj, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 1.0 * (0.03 ** ((now - start) / span))
        limit = cost - T * math.log(1.0 - rng.random())
        ops.clear()
        r = rng.random()
        if r < 0.4:
            _two_switch(adj, ops, A, rng)
        elif r < 0.75:
            _transfer(adj, ops, A, B, d, rng)
        else:
            _rewire(adj, ops, A, rng)
        _fill(adj, ops, side, n, d, rng)
        c2 = _bad_count(n, adj, D)
        if c2 <= limit:
            cost = c2
        else:
            _undo(adj, ops)
    return cost == 0


def _grow_search(n, edges, d, D, deadline, rng):
    """Repeatedly add one vertex per side to the current valid graph and anneal back to validity."""
    adj_lists = [[] for _ in range(n)]
    for u, v in edges:
        adj_lists[u].append(v)
        adj_lists[v].append(u)
    side = _two_colour(n, adj_lists)
    adj = [set(x) for x in adj_lists]
    best = (n, list(edges))
    moore = lib._moore_bound(d, D)
    while deadline - time.monotonic() > 1.0 and n + 2 < moore:
        remaining = deadline - time.monotonic()
        snap_adj = [set(s) for s in adj]
        snap_side = list(side)
        snap_n = n
        adj.append(set())
        adj.append(set())
        side.append(0)
        side.append(1)
        n += 2
        _fill(adj, [], side, n, d, rng)
        ok = _anneal(n, adj, side, d, D, rng, time.monotonic() + 0.5 * remaining)
        if ok:
            E = _edges_of(n, adj, side)
            if lib.is_valid(n, E, d, D):
                best = (n, E)
                continue
        adj, side, n = snap_adj, snap_side, snap_n
    return best


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

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        ara = _ara(d)
        if ara is not None:
            consider(ara[0], ara[1])
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Growth by transfer annealing from the best valid base graph.
    if best[0] < lib._moore_bound(d, D) and time.monotonic() < deadline:
        n2, e2 = _grow_search(best[0], best[1], d, D, deadline, rng)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
