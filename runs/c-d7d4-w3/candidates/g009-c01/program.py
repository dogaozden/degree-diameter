import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases: incidence graphs of PG(2,q) and of the generalized
# quadrangle W(q). These are unchanged from the parent.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Graph helpers on mutable adjacency sets. adj[v] is a set, color[v] in {0,1}.
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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _edges_of(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _snapshot(adj):
    return [set(s) for s in adj]


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


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


def _saturate(adj, color, d, rng):
    """Add edges between opposite sides while both endpoints have spare degree.
    Adding edges never increases a distance, so a valid graph stays valid."""
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


# ----------------------------------------------------------------------------
# Repair-based growth (the new construction).
#
# Instead of attaching a new vertex only when a clean cover exists, we attach
# it to a greedy (randomised) cover of the existing graph and then ANNEAL
# degree-preserving edge switches until the diameter is restored. A failed
# attempt is undone from a snapshot. This lets the graph grow past the points
# where pure cover-growth stalls.
# ----------------------------------------------------------------------------

def _anneal(adj, color, d, D, rng, iters, deadline):
    """Degree-preserving switches (a-b, c-e) -> (a-e, c-b) on side 0 pairs.
    Returns True iff the diameter bound holds at the end. Modifies adj in place."""
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


def _try_grow_one(adj, color, d, D, rng, deadline):
    """Attach one new vertex to a randomised cover, then repair by annealing.
    On failure the graph is restored exactly. Returns True if the graph grew."""
    n = len(adj)
    c = rng.randrange(2)
    cands = [s for s in range(n) if color[s] == c and len(adj[s]) < d]
    if not cands:
        return False
    snap = _snapshot(adj)
    snap_col = list(color)
    ball = _balls_radius(n, adj, D - 1)
    full = (1 << n) - 1
    chosen = _greedy_cover(cands, ball, full, d, rng, True)
    if chosen is None:
        chosen = rng.sample(cands, min(d, len(cands)))
    v = n
    adj.append(set())
    color.append(1 - c)
    for s in chosen:
        adj[s].add(v)
        adj[v].add(s)
    if _anneal(adj, color, d, D, rng, 400, deadline):
        return True
    adj[:] = snap
    color[:] = snap_col
    return False


def _repair_phase(adj, color, d, D, rng, deadline):
    fails = 0
    while time.monotonic() < deadline and fails < 300:
        if _try_grow_one(adj, color, d, D, rng, deadline):
            fails = 0
        else:
            fails += 1


def _perturb(n, edges, d, D, rng, deadline):
    """Delete 1-3 random vertices from a valid graph, saturate, and repair.
    Returns (adj, color) on success, None otherwise."""
    k = rng.choice((1, 2, 3))
    if n <= k + 1:
        return None
    kill = set(rng.sample(range(n), k))
    keep = [v for v in range(n) if v not in kill]
    remap = {v: i for i, v in enumerate(keep)}
    m = len(keep)
    e2 = [(remap[u], remap[v]) for u, v in edges if u not in kill and v not in kill]
    adj = _to_sets(m, e2)
    color = _bipartition(m, adj)
    _saturate(adj, color, d, rng)
    if _anneal(adj, color, d, D, rng, 800, deadline):
        return adj, color
    return None


# ----------------------------------------------------------------------------
# Driver. Budget T = 0.85 * time_limit.
#   1. Structured base (W(q) for D >= 4, else PG(2,q)), saturated.
#   2. Repeated rounds of repair-based growth. Between rounds, with some
#      probability, restart from the best valid graph after a random
#      vertex deletion and repair.
# Every kept graph passes lib.is_valid. The Haar fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase 1: structured base.
    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
    if base is not None:
        n0, e0 = base
        if lib.is_valid(n0, e0, d, D):
            consider(n0, e0)
        else:
            n0, e0 = fallback
    else:
        n0, e0 = fallback

    adj = _to_sets(n0, e0)
    color = _bipartition(n0, adj)
    _saturate(adj, color, d, rng)
    consider(n0, _edges_of(adj))

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase 2: repair-based growth, with restarts from the best graph.
    cur_adj, cur_col = adj, color
    end = at(0.85)
    while time.monotonic() < end:
        if rng.random() < 0.4:
            res = _perturb(best_n, best_e, d, D, rng, min(end, time.monotonic() + 2.0))
            if res is not None:
                cur_adj, cur_col = res
            else:
                cur_adj = _to_sets(best_n, best_e)
                cur_col = _bipartition(best_n, cur_adj)
                _saturate(cur_adj, cur_col, d, rng)
        chunk_end = min(end, time.monotonic() + 3.0)
        _repair_phase(cur_adj, cur_col, d, D, rng, chunk_end)
        consider(len(cur_adj), _edges_of(cur_adj))
        if best_n >= lib.moore_bound(d, D):
            break

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
