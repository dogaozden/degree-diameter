import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs: projective plane incidence and generalized quadrangle W(q).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Graph state helpers. Graph = (n, adj, col, sides): adj is a list of sets,
# col[v] in {0, 1} is the bipartition side, sides[s] lists vertices of side s.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
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


def _cost(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included). Zero means valid."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal(n, adj, col, sides, d, D, rng, iters, deadline):
    """Metropolis search over degree-preserving edge rewirings and spare-degree edge additions.

    Keeps bipartiteness and degree <= d by construction; minimises the bad-pair count.
    Returns the final cost (0 means the graph has diameter <= D).
    """
    cost = _cost(n, adj, D)
    T0, T1 = 2.0, 0.2
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = T0 + (T1 - T0) * it / max(1, iters - 1)
        r = rng.random()
        if r < 0.8:
            a = rng.randrange(n)
            if not adj[a]:
                continue
            b = rng.choice(tuple(adj[a]))
            # Replace one endpoint x of edge (x, y) by a new vertex on x's side.
            if rng.random() < 0.5:
                x, y = a, b
            else:
                x, y = b, a
            new = rng.choice(sides[col[x]])
            if new == x or new in adj[y] or len(adj[new]) >= d:
                continue
            adj[x].discard(y)
            adj[y].discard(x)
            adj[new].add(y)
            adj[y].add(new)
            c2 = _cost(n, adj, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                adj[new].discard(y)
                adj[y].discard(new)
                adj[x].add(y)
                adj[y].add(x)
        else:
            # Add an edge between two vertices with spare degree.
            x = rng.choice(sides[0])
            y = rng.choice(sides[1])
            if y in adj[x] or len(adj[x]) >= d or len(adj[y]) >= d:
                continue
            adj[x].add(y)
            adj[y].add(x)
            c2 = _cost(n, adj, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                adj[x].discard(y)
                adj[y].discard(x)
    return cost


def _add_vertex(n, adj, col, sides, s, d, rng):
    """Append a new vertex on side s, joined to up to d vertices of the opposite side.

    Full opposite-side vertices give up one random edge so the degree bound holds.
    Returns the new vertex count.
    """
    v = n
    adj.append(set())
    col.append(s)
    sides[s].append(v)
    opp = sides[1 - s]
    k = min(d, len(opp))
    for b in rng.sample(opp, k):
        if len(adj[b]) >= d:
            a = rng.choice(tuple(adj[b]))
            adj[a].discard(b)
            adj[b].discard(a)
        adj[v].add(b)
        adj[b].add(v)
    return n + 1


def _to_edges(n, adj):
    return [(a, b) for a in range(n) for b in adj[a] if a < b]


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
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Grow-and-repair: add one vertex at a time, then anneal edges until the
    # diameter is restored. A failed attempt is rolled back to the last valid graph.
    n, edges = best
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _bipartition(n, adj)
    sides = [[v for v in range(n) if col[v] == 0], [v for v in range(n) if col[v] == 1]]

    cur_best_n, cur_best_edges = n, list(edges)
    ITERS = 600

    while time.monotonic() < deadline:
        snap_n = n
        snap_adj = [set(x) for x in adj]
        snap_col = list(col)
        snap_sides = [list(sides[0]), list(sides[1])]

        s = rng.randrange(2)
        n2 = _add_vertex(n, adj, col, sides, s, d, rng)
        cost = _anneal(n2, adj, col, sides, d, D, rng, ITERS, deadline)

        if cost == 0:
            n = n2
            if n > cur_best_n:
                cur_best_n = n
                cur_best_edges = _to_edges(n, adj)
        else:
            n = snap_n
            adj = snap_adj
            col = snap_col
            sides = snap_sides

    if cur_best_n > best[0]:
        consider(cur_best_n, cur_best_edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
