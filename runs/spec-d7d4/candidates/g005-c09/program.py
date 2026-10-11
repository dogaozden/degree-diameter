import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: projective plane (D = 3) and generalized quadrangle W(q)
# (D >= 4). Both are bipartite with points on side 0 and lines on side 1.
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
    """W(q) for the largest prime power q with q + 1 <= d (q capped for build speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared adjacency utilities. Adjacency is a list of sets so edges can be
# rewired in place.
# ----------------------------------------------------------------------------

def _balls_sets(n, adj, r):
    """Bitmask of all vertices within distance r of each vertex."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return ball


def _bad_pairs_sets(n, adj, D):
    """Number of unordered pairs at distance > D (zero means diameter <= D)."""
    ball = _balls_sets(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _orient_colors(n, E0):
    """2-colour a connected-or-not bipartite graph given as an edge list."""
    adj = [[] for _ in range(n)]
    for u, v in E0:
        adj[u].append(v)
        adj[v].append(u)
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


def _cover_search(ball, cands, full, d, rng, budget):
    """Find <= d candidates whose radius balls cover `full`; return list or None."""
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


def _try_add(n, adj, color, E, Eset, d, D, rng, budget):
    """Add one vertex whose neighbourhood covers every vertex within D-1.
    Such a vertex keeps the diameter <= D. Returns (new_n, success)."""
    ball = _balls_sets(n, adj, D - 1)
    full = (1 << n) - 1
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
            adj.append(set())
            for s in chosen:
                adj[s].add(v)
                adj[v].add(s)
                e = (s, v) if color[s] == 0 else (v, s)
                E.append(e)
                Eset.add(e)
            return n + 1, True
    return n, False


def _saturate(n, adj, color, E, Eset, d, rng):
    """Add edges between spare-degree vertices on opposite sides (only shortens paths)."""
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)
            E.append((a, b))
            Eset.add((a, b))


def _rewire(E, Eset, adj, i, j, old, new):
    """Replace edges old=((a,b),(c,d)) with new=((a,d),(c,b)) at list slots i, j."""
    for x, y in old:
        adj[x].discard(y)
        adj[y].discard(x)
        Eset.discard((x, y))
    for x, y in new:
        adj[x].add(y)
        adj[y].add(x)
        Eset.add((x, y))
    E[i] = new[0]
    E[j] = new[1]


def _rebuild(n, E):
    adj = [set() for _ in range(n)]
    Eset = set()
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
        Eset.add((u, v))
    return adj, Eset


# ----------------------------------------------------------------------------
# NEW HELPER: degree-preserving 2-switch annealing with cover-based growth.
#
# State: a bipartite graph on n vertices with maximum degree d, possibly with
# some diameter violations. Cost = number of vertex pairs at distance > D.
# Moves are degree-preserving edge swaps (a,b),(c,e) -> (a,e),(c,b), which
# are accepted by a Metropolis rule on the cost. Whenever the cost reaches 0,
# we try to append a vertex with an exact cover of radius D-1. This lets the
# search "release" degree from tight regions and then spend it on growth.
# ----------------------------------------------------------------------------

def _anneal_grow(n, E0, d, D, deadline, rng):
    color = _orient_colors(n, E0)
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in E0]
    adj, Eset = _rebuild(n, E)
    _saturate(n, adj, color, E, Eset, d, rng)
    cost = _bad_pairs_sets(n, adj, D)

    best = None
    best_n = 0
    if cost == 0:
        best = (n, list(E), list(color))
        best_n = n

    T = 0.4
    try_add = cost == 0
    since = 0
    while time.monotonic() < deadline:
        if try_add and cost == 0:
            try_add = False
            grew = False
            while time.monotonic() < deadline:
                n2, ok = _try_add(n, adj, color, E, Eset, d, D, rng, 400)
                if not ok:
                    break
                n = n2
                grew = True
                _saturate(n, adj, color, E, Eset, d, rng)
            if grew:
                cost = _bad_pairs_sets(n, adj, D)
                if cost == 0 and n > best_n:
                    best = (n, list(E), list(color))
                    best_n = n
                    since = 0

        m = len(E)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e2 = E[j]
        if a == c or b == e2 or e2 in adj[a] or b in adj[c]:
            continue
        old = ((a, b), (c, e2))
        new = ((a, e2), (c, b))
        _rewire(E, Eset, adj, i, j, old, new)
        c2 = _bad_pairs_sets(n, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            since += 1
            if cost == 0:
                try_add = True
        else:
            _rewire(E, Eset, adj, i, j, new, old)

        # Restart from the best snapshot after a long stall, with a fresh temperature.
        if best is not None and since > 3000:
            bn, be, bc = best
            n = bn
            E = list(be)
            color = list(bc)
            adj, Eset = _rebuild(n, E)
            cost = 0
            try_add = True
            since = 0
            T = 0.25 + 0.4 * rng.random()

    if best is None:
        return None
    return best[0], best[1]


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Base graph: projective plane for D = 3, generalized quadrangle for D >= 4.
    base = None
    if D == 3:
        base = _best_pg(d)
    elif D >= 4:
        base = _best_gq(d)
    if base is None:
        base = lib.haar_graph(d, range(d))
    consider(base[0], base[1])

    grow_end = start + 0.8 * time_limit
    res = _anneal_grow(base[0], base[1], d, D, grow_end, rng)
    if res is not None:
        consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
