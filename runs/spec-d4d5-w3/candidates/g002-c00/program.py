import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline constructions: projective plane and generalized quadrangle W(q),
# grown by diameter-preserving cover extension.
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


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


def _greedy_cover(cands, ball, full, d, rng, randomize):
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
# New family: degree-constrained bipartite annealing with growth.
#
# Start from a valid graph and repeatedly add one vertex on each side. The
# new vertices are then attached by annealing over moves that keep the graph
# bipartite with max degree d:
#   add      : join a deficient left vertex to a deficient right vertex
#   double   : 2-switch two edges (degree-preserving)
#   slide-L  : move one endpoint of an edge to a deficient left vertex
#   slide-R  : move one endpoint of an edge to a deficient right vertex
# The cost is the number of ordered vertex pairs at distance > D. Adds never
# increase the cost, so the walk can only lose ground through the other moves.
# ----------------------------------------------------------------------------

def _cost(n, adj, D):
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


def _pick_deficient(V, adj, d, rng):
    for _ in range(60):
        v = V[rng.randrange(len(V))]
        if len(adj[v]) < d:
            return v
    return None


def _pick_edge(V, adj, rng):
    """Return (v, u): v from V with a neighbour u, or None."""
    for _ in range(40):
        a = V[rng.randrange(len(V))]
        if adj[a]:
            return a, rng.choice(tuple(adj[a]))
    return None


def _propose(adj, Lv, Rv, d, rng):
    """Return a list of ops (flag, a, b) with flag 1 = add, 0 = remove, or None."""
    r = rng.random()
    if r < 0.2:
        a = _pick_deficient(Lv, adj, d, rng)
        b = _pick_deficient(Rv, adj, d, rng)
        if a is None or b is None or b in adj[a]:
            return None
        return [(1, a, b)]
    if r < 0.6:
        e1 = _pick_edge(Lv, adj, rng)
        e2 = _pick_edge(Lv, adj, rng)
        if e1 is None or e2 is None:
            return None
        a1, b1 = e1
        a2, b2 = e2
        if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            return None
        return [(0, a1, b1), (0, a2, b2), (1, a1, b2), (1, a2, b1)]
    if r < 0.8:
        x = _pick_deficient(Lv, adj, d, rng)
        e = _pick_edge(Lv, adj, rng)
        if x is None or e is None:
            return None
        a, b = e
        if a == x or b in adj[x]:
            return None
        return [(0, a, b), (1, x, b)]
    y = _pick_deficient(Rv, adj, d, rng)
    e = _pick_edge(Rv, adj, rng)
    if y is None or e is None:
        return None
    b, a = e  # b in R, a in L
    if b == y or y in adj[a]:
        return None
    return [(0, a, b), (1, a, y)]


def _apply(adj, ops):
    for flag, a, b in ops:
        if flag:
            adj[a].add(b)
            adj[b].add(a)
        else:
            adj[a].discard(b)
            adj[b].discard(a)


def _undo(adj, ops):
    for flag, a, b in reversed(ops):
        if flag:
            adj[a].discard(b)
            adj[b].discard(a)
        else:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(n, adj, Lv, Rv, d, D, deadline, rng):
    """Anneal until cost is zero (True) or the deadline passes (False)."""
    cur = _cost(n, adj, D)
    T0, Tend, chunk = 1.5, 0.15, 2000
    t = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return False
        frac = (t % chunk) / chunk
        T = T0 * (Tend / T0) ** frac
        t += 1
        ops = _propose(adj, Lv, Rv, d, rng)
        if ops is None:
            continue
        _apply(adj, ops)
        c2 = _cost(n, adj, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
        else:
            _undo(adj, ops)
    return True


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    moore = lib.moore_bound(d, D)
    if D == 2 or best_n >= moore:
        return best

    # Baseline: generalized quadrangle for D >= 4, projective plane otherwise,
    # grown by cover extension. This is the graph the annealer starts from.
    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None:
        base = _best_pg(d)
    if base is not None:
        consider(base[0], base[1])
        n0, e0 = _grow(base[0], base[1], d, D, start + 0.3 * (deadline - start), rng)
        consider(n0, e0)

    # Growth phase: add one vertex per side and anneal until valid again.
    n, edges = best
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(n, adj)
    Lv = [v for v in range(n) if color[v] == 0]
    Rv = [v for v in range(n) if color[v] == 1]

    while time.monotonic() < deadline:
        if n + 2 > moore:
            break
        Lv.append(n)
        Rv.append(n + 1)
        adj.append(set())
        adj.append(set())
        n += 2
        if not _anneal(n, adj, Lv, Rv, d, D, deadline, rng):
            break
        e = [(u, v) for u in range(n) for v in adj[u] if u < v]
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
