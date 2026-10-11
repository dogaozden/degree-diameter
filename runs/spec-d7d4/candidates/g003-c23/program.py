import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: projective plane (D = 3) and generalized quadrangle (D >= 4).
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
# Cover-based vertex extension and edge saturation (diameter-preserving growth).
# ----------------------------------------------------------------------------

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
    attempts_max = 600 if D >= 4 else 200

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(attempts_max):
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
    for _ in range(20):
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
# New search: degree-preserving edge-swap annealing on bipartite graphs.
#
# State: color[v] in {0,1}; nb[v] = set of neighbours; E = list of (a, b) with
# color[a] == 0 and color[b] == 1, one entry per edge.
# Moves keep every degree <= d and the graph bipartite. Growth inserts a new
# A-vertex and B-vertex by subdividing a matching of d edges, which keeps all
# degrees unchanged. Cost = number of unordered vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _state(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    nb = [set(a) for a in adj]
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    return list(color), nb, E


def _cost(n, nb, D):
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in nb[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _set_edge(nb, E, i, new):
    a, b = E[i]
    nb[a].discard(b)
    nb[b].discard(a)
    a2, b2 = new
    nb[a2].add(b2)
    nb[b2].add(a2)
    E[i] = new


def _move(color, nb, E, d, rng):
    """Apply one random move; return list of (index, old_edge) for undo, or None if no move was made."""
    m = len(E)
    if m < 2:
        return None
    n = len(color)
    if rng.random() < 0.6:
        # Degree-preserving double edge swap.
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            return None
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in nb[a1] or b1 in nb[a2]:
            return None
        olds = [(i, E[i]), (j, E[j])]
        _set_edge(nb, E, i, (a1, b2))
        _set_edge(nb, E, j, (a2, b1))
        return olds
    # Rewire one endpoint onto a vertex with spare degree.
    i = rng.randrange(m)
    a, b = E[i]
    old = E[i]
    if rng.random() < 0.5:
        cands = [v for v in range(n)
                 if color[v] == 1 and v != b and v not in nb[a] and len(nb[v]) < d]
        if not cands:
            return None
        c = rng.choice(cands)
        _set_edge(nb, E, i, (a, c))
    else:
        cands = [u for u in range(n)
                 if color[u] == 0 and u != a and u not in nb[b] and len(nb[u]) < d]
        if not cands:
            return None
        c = rng.choice(cands)
        _set_edge(nb, E, i, (c, b))
    return [(i, old)]


def _anneal(color, nb, E, d, D, rng, deadline, iters):
    n = len(color)
    cur = _cost(n, nb, D)
    T = 1.0
    for it in range(iters):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        undo = _move(color, nb, E, d, rng)
        if undo is None:
            continue
        new = _cost(n, nb, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            for idx, old in reversed(undo):
                _set_edge(nb, E, idx, old)
        T = max(0.15, T * 0.999)
    return cur


def _insert_pair(color, nb, E, d, rng):
    """Add an A-vertex v and a B-vertex w; subdivide a matching of d edges between them. Degrees stay <= d."""
    order = list(range(len(E)))
    rng.shuffle(order)
    used = set()
    match = []
    for i in order:
        a, b = E[i]
        if a in used or b in used:
            continue
        used.add(a)
        used.add(b)
        match.append(i)
        if len(match) == d:
            break
    if len(match) < d:
        return False
    v = len(color)
    color.append(0)
    nb.append(set())
    w = len(color)
    color.append(1)
    nb.append(set())
    for i in match:
        a, b = E[i]
        _set_edge(nb, E, i, (v, b))
        E.append((a, w))
        nb[a].add(w)
        nb[w].add(a)
    return True


def _phase_anneal(n0, edges0, d, D, deadline, rng, consider):
    color0, nb0, E0 = _state(n0, edges0)
    base = (color0, nb0, E0)
    while time.monotonic() < deadline:
        color = list(base[0])
        nb = [set(s) for s in base[1]]
        E = list(base[2])
        if not _insert_pair(color, nb, E, d, rng):
            return
        n = len(color)
        cost = _anneal(color, nb, E, d, D, rng, deadline, 3000)
        if cost == 0:
            consider(n, list(E))
            base = (color, nb, E)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = [fb_n, list(fb_e)]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, list(e)

    # Phase 1: algebraic base plus cover-based growth.
    try:
        base = None
        grow_until = start
        if D == 3:
            base = _best_pg(d)
            grow_until = start + 0.2 * time_limit
        elif D >= 4:
            base = _best_gq(d)
            grow_until = start + 0.4 * time_limit
        if base is not None:
            consider(base[0], base[1])
            n2, e2 = _grow(base[0], base[1], d, D, grow_until, rng)
            consider(n2, e2)
    except Exception:
        pass

    # Phase 2: annealing growth from the best graph found so far.
    try:
        moore = getattr(lib, "_moore_bound", None)
        bound = moore(d, D) if moore is not None else 10 ** 9
        if best[0] < bound and time.monotonic() < deadline:
            _phase_anneal(best[0], best[1], d, D, deadline, rng, consider)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = [fb_n, list(fb_e)]
    return best[0], best[1]
