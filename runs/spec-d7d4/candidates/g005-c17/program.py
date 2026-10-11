import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
#   D = 3: projective plane incidence graph PG(2, q) with q + 1 <= d.
#   D >= 4: incidence graph of the generalized quadrangle W(q) with q + 1 <= d.
# ----------------------------------------------------------------------------

def _best_pg(d):
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Graph helpers on adjacency lists (vertices 0..n-1, colour = side of bipartition).
# ----------------------------------------------------------------------------

def _to_adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _edges_of(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


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


def _balls_radius(n, adj, r):
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


def _cover_search(ball, cands, full, d, rng, budget):
    """Find <= d candidates whose radius balls cover `full`; return list or None (budgeted DFS)."""
    used = set()
    chosen = []
    nodes = [0]

    def rec(covered, depth):
        if covered == full:
            return True
        if depth >= d or nodes[0] >= budget:
            return False
        nodes[0] += 1
        rem = full & ~covered
        free = [s for s in cands if s not in used]
        gains = {s: (ball[s] & rem).bit_count() for s in free}
        best = max(gains.values(), default=0)
        if best == 0 or rem.bit_count() > best * (d - depth):
            return False
        bits = []
        x = rem
        while x:
            low = x & -x
            bits.append(low.bit_length() - 1)
            x ^= low
        sample = rng.sample(bits, min(6, len(bits)))
        best_opts = None
        for w in sample:
            opts = [s for s in free if gains[s] and (ball[s] >> w) & 1]
            if best_opts is None or len(opts) < len(best_opts):
                best_opts = opts
        if not best_opts:
            return False
        rng.shuffle(best_opts)
        best_opts.sort(key=lambda s: -gains[s])
        for s in best_opts:
            used.add(s)
            chosen.append(s)
            if rec(covered | ball[s], depth + 1):
                return True
            used.discard(s)
            chosen.pop()
            if nodes[0] >= budget:
                break
        return False

    return list(chosen) if rec(0, 0) else None


def _regrow(adj, color, d, D, deadline, rng, budget):
    """Repeatedly add a vertex whose neighbourhood (spare degree, other side) covers all within D-1.

    Mutates adj and color in place.
    """
    while time.monotonic() < deadline:
        n = len(adj)
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        placed = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [s for s in range(n) if color[s] == 1 - c and len(adj[s]) < d]
            if not cands:
                continue
            chosen = _cover_search(ball, cands, full, d, rng, budget)
            if chosen:
                v = n
                color.append(c)
                adj.append([])
                for s in chosen:
                    adj[s].append(v)
                    adj[v].append(s)
                placed = True
                break
        if not placed:
            return


def _saturate(adj, color, d, rng):
    """Add opposite-side edges between vertices with spare degree. Preserves diameter and bipartiteness."""
    n = len(adj)
    nbr = [set(a) for a in adj]
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in nbr[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d:
            adj[a].append(b)
            adj[b].append(a)


# ----------------------------------------------------------------------------
# NEW: ball-ruin and cover-regrow large-neighbourhood search (LNS).
#
# A state is a valid graph. A move deletes a locally connected ball of vertices
# (ruin), which frees spare degree on their neighbours, then regrows by exact
# cover insertion (recreate) and saturates leftover degree. The move is accepted
# if the result is still valid and not smaller (plateau moves let the structure
# drift to new regions where new vertices can be inserted). The best valid graph
# seen is kept, so the search can never regress.
# ----------------------------------------------------------------------------

def _bfs_order(adj, start, limit):
    seen = {start}
    order = [start]
    i = 0
    while i < len(order) and len(order) < limit:
        u = order[i]
        i += 1
        for v in adj[u]:
            if v not in seen:
                seen.add(v)
                order.append(v)
    return order


def _ruin(adj, color, kill, rng):
    """Remove a ball (or a random set, with some probability) of `kill` vertices; relabel to 0..n'-1."""
    n = len(adj)
    if rng.random() < 0.7:
        gone = set(_bfs_order(adj, rng.randrange(n), kill))
    else:
        gone = set(rng.sample(range(n), kill))
    keep = [v for v in range(n) if v not in gone]
    idx = {old: i for i, old in enumerate(keep)}
    nadj = [[idx[u] for u in adj[old] if u not in gone] for old in keep]
    ncol = [color[old] for old in keep]
    return nadj, ncol


def _lns(adj, col, d, D, deadline, rng, moore):
    adj = [list(a) for a in adj]
    col = list(col)
    _regrow(adj, col, d, D, deadline, rng, 400)
    _saturate(adj, col, d, rng)
    cur_adj, cur_col = adj, col
    cur_n = len(cur_adj)
    cur_e = _edges_of(cur_adj)
    best = None
    if lib.is_valid(cur_n, cur_e, d, D):
        best = (cur_n, cur_e)
    if best is None:
        return None

    while time.monotonic() < deadline and cur_n < moore:
        kill = rng.choice((1, 1, 2, 2, 3, 4, 6))
        nadj, ncol = _ruin(cur_adj, cur_col, kill, rng)
        _regrow(nadj, ncol, d, D, deadline, rng, 200)
        _saturate(nadj, ncol, d, rng)
        n2 = len(nadj)
        if n2 < cur_n:
            continue
        e2 = _edges_of(nadj)
        if not lib.is_valid(n2, e2, d, D):
            continue
        cur_adj, cur_col, cur_n = nadj, ncol, n2
        if n2 > best[0]:
            best = (n2, e2)
    return best


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    base = None
    if D == 3:
        base = _best_pg(d)
    elif D >= 4:
        base = _best_gq(d)
    if base is None or not lib.is_valid(base[0], base[1], d, D):
        base = fallback

    bn, be = base
    moore = lib._moore_bound(d, D)
    if bn >= moore:
        return bn, be

    adj = _to_adj(bn, be)
    col = _bipartition(bn, adj)
    res = _lns(adj, col, d, D, deadline, rng, moore)
    if res is not None and res[0] > bn and lib.is_valid(res[0], res[1], d, D):
        return res
    return base
