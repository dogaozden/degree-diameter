import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base graphs with an arc extension (D = 3).
#
# PG(2, q) incidence graph, points 0..m-1 (side 0), lines m..2m-1 (side 1).
# Every vertex has degree q+1, so spare s = d - q - 1. Pick an arc S (indices
# usable both as points and as dual lines) with loads <= s, and add an A-vertex
# (side 0) on the lines through each P in S and a B-vertex (side 1) on the
# points of each line j in S.
#
# NEW HELPER: capacitated cover augmentation. A new side-0 vertex x is valid
# (for D = 3) iff its neighbourhood N consists of side-1 vertices with spare
# capacity, and N dominates every existing side-0 vertex. Then every side-0
# vertex is at distance 2 from x, and every side-1 vertex w has a side-0
# neighbour a adjacent to N, so dist(x, w) <= 3. Existing distances are only
# shortened by adding vertices, so the graph stays valid. This is a greedy
# set cover with capacities, chosen with random tie-breaks. Kicks remove one
# added vertex, retry, and keep the result only if it is still valid and not
# smaller.
# ----------------------------------------------------------------------------


def _pg(q):
    """Return (m, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, point_lines, line_points, index


def _loads_ok(S, s, m, pl, lp):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, trials):
    """Randomized greedy arc with all loads <= s."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _base(q, d, rng):
    """Return (adj, side) of the arc-extended PG(2,q) graph with spare s = d-q-1, or None."""
    s = d - q - 1
    if s < 0:
        return None
    m, pl, lp, index = _pg(q)
    S = []
    if s >= 1:
        S = _greedy_arc(m, s, pl, lp, rng, 30)
        if s >= 2:
            cs = _conic(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp) and len(cs) > len(S):
                S = cs
    if not _loads_ok(S, s, m, pl, lp):
        return None
    k = len(S)
    n = 2 * m + 2 * k
    adj = [set() for _ in range(n)]

    def link(u, v):
        adj[u].add(v)
        adj[v].add(u)

    for u in range(m):
        for L in pl[u]:
            link(u, m + L)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in pl[P]:
            link(x, m + L)
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            link(Q, b)
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return adj, side


# ----------------------------------------------------------------------------
# Capacitated cover augmentation (new helper).
# ----------------------------------------------------------------------------

def _cover(adj, side, alive, d, sx, rng):
    """Greedy capacitated cover: chosen opposite-side vertices with spare capacity
    whose neighbourhoods cover every alive side-sx vertex. Returns list or None."""
    N = len(adj)
    opp = 1 - sx
    uncovered = {u for u in range(N) if alive[u] and side[u] == sx}
    if not uncovered:
        return None
    cand = [w for w in range(N) if alive[w] and side[w] == opp and len(adj[w]) < d]
    chosen = []
    while uncovered:
        if len(chosen) >= d or not cand:
            return None
        best_g = 0
        pool = []
        for w in cand:
            g = len(uncovered.intersection(adj[w]))
            if g > best_g:
                best_g = g
                pool = [w]
            elif g == best_g and g > 0:
                pool.append(w)
        if best_g == 0:
            return None
        w = rng.choice(pool)
        chosen.append(w)
        cand.remove(w)
        uncovered.difference_update(adj[w])
    return chosen


def _add(adj, side, alive, sx, chosen):
    """Append a new vertex of side sx joined to chosen; return its id."""
    x = len(adj)
    adj.append(set())
    side.append(sx)
    alive.append(True)
    for w in chosen:
        adj[w].add(x)
        adj[x].add(w)
    return x


def _kill(adj, alive, x):
    """Remove vertex x and its edges."""
    for w in adj[x]:
        adj[w].discard(x)
    adj[x] = set()
    alive[x] = False


def _count(alive, n0):
    """Number of alive added vertices (ids >= n0)."""
    return sum(1 for v in range(n0, len(alive)) if alive[v])


def _valid_adj(adj, alive, d, D):
    """Return (n, edges) relabelled if the current graph is valid, else None."""
    E = [(u, v) for u in range(len(adj)) if alive[u] for v in adj[u] if u < v]
    if not E:
        return None
    n, E2 = lib.relabel(E)
    if lib.is_valid(n, E2, d, D):
        return n, E2
    return None


def _kick(adj, side, alive, n0, d, D, rng):
    """Remove a random added vertex, try to re-add up to 4 vertices, keep if no
    smaller and still valid; otherwise restore the snapshot."""
    new_ids = [v for v in range(n0, len(adj)) if alive[v]]
    if not new_ids:
        return
    snap = ([set(a) for a in adj], list(side), list(alive))
    before = _count(alive, n0)
    _kill(adj, alive, rng.choice(new_ids))
    for _ in range(4):
        sx = rng.randrange(2)
        ch = _cover(adj, side, alive, d, sx, rng)
        if ch is not None:
            _add(adj, side, alive, sx, ch)
    ok = _count(alive, n0) >= before and _valid_adj(adj, alive, d, D) is not None
    if not ok:
        adj[:] = snap[0]
        side[:] = snap[1]
        alive[:] = snap[2]


def _augment(adj, side, alive, n0, d, D, rng, deadline):
    """Add vertices while covers exist; kick when stuck."""
    if all(len(adj[v]) >= d for v in range(n0)):
        return
    fails = 0
    while time.monotonic() < deadline:
        sx = rng.randrange(2)
        ch = _cover(adj, side, alive, d, sx, rng)
        if ch is not None:
            _add(adj, side, alive, sx, ch)
            fails = 0
            continue
        fails += 1
        if fails >= 25:
            fails = 0
            _kick(adj, side, alive, n0, d, D, rng)


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4), restricted to small q.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q); diameter 4."""
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

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(res):
        nonlocal best, best_n
        if res is None:
            return
        n, E = res
        if n > best_n and lib.is_valid(n, E, d, D):
            best = (n, E)
            best_n = n

    if D == 3:
        # Top prime powers q <= d-1, each gets an equal share of the budget.
        qs = sorted([q for q in range(2, d) if lib.is_prime_power(q)], reverse=True)[:4]
        for idx, q in enumerate(qs):
            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0:
                break
            sub = now + remaining / (len(qs) - idx)
            base = _base(q, d, rng)
            if base is None:
                continue
            adj, side = base
            n0 = len(adj)
            alive = [True] * n0
            if _valid_adj(adj, alive, d, D) is None:
                continue
            consider(_valid_adj(adj, alive, d, D))
            _augment(adj, side, alive, n0, d, D, rng, sub)
            consider(_valid_adj(adj, alive, d, D))

    elif D >= 4:
        for q in range(min(d - 1, 5), 1, -1):
            if lib.is_prime_power(q):
                consider(_gq_w(q))
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
