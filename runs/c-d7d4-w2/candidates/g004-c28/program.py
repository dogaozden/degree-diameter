import itertools
import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
    """
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
# ----------------------------------------------------------------------------

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
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices. Returns list or None."""
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


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list.

    Adding cross-side edges keeps the graph bipartite and degrees <= d, and can only
    shorten distances, so a valid graph stays valid.
    """
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
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
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
# Twin duplication.
#
# A vertex v' with N(v') = N(v), v' not adjacent to v, is a "twin" of v. In any
# graph, non-adjacent twins are at the same distance from every other vertex,
# and at distance 2 from each other. So duplicating a vertex never breaks the
# diameter bound (for D >= 2), keeps the graph bipartite (v' is on v's side),
# and needs only spare degree on the neighbours of v.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    """Greedily add twins in random order while neighbours have spare degree."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    """One randomized pipeline: mix twin duplication with cover growth and saturation."""
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# Voltage lifts over small groups (new construction).
#
# A base multigraph with `a` vertices per side is lifted over a finite group G
# (cyclic or semidirect Z_m x| Z_k). Each base vertex has degree d, so the lift
# is d-regular with 2*a*|G| vertices. Left multiplication by G is an automorphism
# acting transitively on every fibre, so the distances from one representative
# per base vertex decide the diameter. Voltages are found by hill climbing on the
# number of vertices missed by the depth-D balls of those representatives.
# ----------------------------------------------------------------------------

VOLTAGE_SLICE = 3.0
_GROUP_CACHE = {}


def _groups_of_order(N):
    """(order, mul) for semidirect products Z_m x| Z_k with m*k = N, over all valid actions r."""
    if N in _GROUP_CACHE:
        return _GROUP_CACHE[N]
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(1, m + 1):
            try:
                order, mul, _ = lib.semidirect_group(m, k, r)
            except ValueError:
                continue
            out.append((order, mul))
    _GROUP_CACHE[N] = out
    return out


def _lift_search(d, D, a, N, mul, deadline, rng):
    """Hill-climb voltages of a base with `a` vertices per side over a group of order N.

    Returns (n, edges) for a valid d-regular lift, or None if the deadline passes first.
    """
    if N <= d:
        return None
    T = 2 * a * N
    M = [[mul(x, g) for g in range(N)] for x in range(N)]
    if a == 1:
        k = [[d]]
    else:
        s = rng.randint(1, d - 1)
        k = [[s, d - s], [d - s, s]]
    # Base pairs (u in side A = 0..a-1, v in side B = a..2a-1, number of darts).
    pairs = [(i, a + j, k[i][j]) for i in range(a) for j in range(a)]

    def fresh():
        darts = []
        for u, v, c in pairs:
            darts.extend((u, v, g) for g in rng.sample(range(N), c))
        return darts

    def lift_adj(darts):
        adj = [[] for _ in range(T)]
        for u, v, g in darts:
            for x in range(N):
                p = u * N + x
                q = v * N + M[x][g]
                adj[p].append(q)
                adj[q].append(p)
        return adj

    def bad(adj):
        total = 0
        for s in range(2 * a):
            src = s * N
            seen = {src}
            frontier = [src]
            for _ in range(D):
                nxt = []
                for p in frontier:
                    for q in adj[p]:
                        if q not in seen:
                            seen.add(q)
                            nxt.append(q)
                if not nxt:
                    break
                frontier = nxt
            total += T - len(seen)
        return total

    darts = fresh()
    cur = bad(lift_adj(darts))
    stall = 0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        if stall > 1500:
            darts = fresh()
            cur = bad(lift_adj(darts))
            stall = 0
            continue
        idx = rng.randrange(len(darts))
        u, v, g_old = darts[idx]
        taken = {g for uu, vv, g in darts if uu == u and vv == v}
        g_new = rng.randrange(N)
        while g_new in taken:
            g_new = rng.randrange(N)
        darts[idx] = (u, v, g_new)
        new = bad(lift_adj(darts))
        if new <= cur:
            stall = 0 if new < cur else stall + 1
            cur = new
        else:
            darts[idx] = (u, v, g_old)
            stall += 1
    adj = lift_adj(darts)
    edges = sorted({(min(p, q), max(p, q)) for p in range(T) for q in adj[p]})
    return T, edges


def _voltage_stage(d, D, best, deadline, rng, consider):
    """Search group lifts with orders above the current best, smallest order first.

    `best()` returns the current best vertex count; `consider(n, e)` returns True on improvement.
    """
    if d < 2 or D < 2:
        return
    moore = lib.moore_bound(d, D)
    tasks = []
    for a in (1, 2):
        per = 2 * a
        for N in range(best() // per + 1, moore // per + 1):
            if N > d:
                tasks.append((per * N, a, N))
    tasks.sort()
    while time.monotonic() < deadline:
        active = [t for t in tasks if t[0] > best()]
        if not active:
            break
        for total, a, N in active:
            if time.monotonic() >= deadline:
                break
            if total <= best():
                continue
            order, mul = rng.choice(_groups_of_order(N))
            end = min(deadline, time.monotonic() + VOLTAGE_SLICE)
            res = _lift_search(d, D, a, N, mul, end, rng)
            if res is not None:
                consider(*res)


# ----------------------------------------------------------------------------
# Large-neighbourhood search (kill, repair, regrow).
#
# Delete 1-4 vertices from a valid graph. Their neighbours regain spare degree,
# but distances may grow. Repair the diameter with bipartite double-edge
# switches (degrees preserved), then regrow with cover vertices and saturation.
# Cover growth keeps the diameter bound, so every accepted state stays valid.
# The walk is anchored: if it drifts too far below its best graph, it returns
# to that best graph instead of wandering off the plateau.
# ----------------------------------------------------------------------------

def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(adj, color, d, D, side, rng):
    """Append a vertex on the opposite side of `side`, joined to a greedy cover of `side`."""
    n = len(adj)
    ball = _balls_radius(n, adj, D - 1)
    covered = 0
    chosen = []
    cands = [s for s in range(n) if color[s] == side]
    for _ in range(d):
        best_s, best_g = None, -1.0
        for s in cands:
            if s in chosen:
                continue
            g = (ball[s] & ~covered).bit_count() + 0.5 * rng.random()
            if g > best_g:
                best_s, best_g = s, g
        if best_s is None:
            break
        chosen.append(best_s)
        covered |= ball[best_s]
    v = n
    adj.append(set())
    color.append(1 - side)
    for s in chosen:
        if len(adj[s]) >= d:
            t = rng.choice(tuple(adj[s]))
            adj[s].discard(t)
            adj[t].discard(s)
        adj[s].add(v)
        adj[v].add(s)
    return v


def _fill(adj, color, d, rng):
    """Add cross-side edges between deficient vertices (only helps the diameter)."""
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    """Bipartite double-edge switches (degrees unchanged) minimising bad pairs. True if cost reaches 0."""
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
        # Switch a-b, c-e into a-e, c-b (a, c on side 0; b, e on side 1).
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


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
        if k >= cur_n:
            break
        kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        # Accept sideways and slightly downward moves to drift across the plateau.
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            # Drifted too far below the best graph: return to it.
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Redundant-edge pruning, then regrow.
#
# An edge is redundant if deleting it keeps every pair within distance D. Deleting
# redundant edges frees degree on both endpoints without breaking validity. The
# freed slots are then used by cover growth, which can add new vertices that a
# fixed edge set could not accommodate. Every intermediate graph is checked with
# the exact bad-pair count, so the walk only moves through valid graphs.
# ----------------------------------------------------------------------------

def _prune_redundant(n, edges, D, rng, deadline, max_tests):
    """Delete random redundant edges (keeping diameter <= D). Returns the pruned edge list."""
    adj = _to_sets(n, edges)
    cand = list(edges)
    rng.shuffle(cand)
    tests = 0
    for u, v in cand:
        if tests >= max_tests or time.monotonic() > deadline:
            break
        if v not in adj[u]:
            continue
        tests += 1
        adj[u].discard(v)
        adj[v].discard(u)
        if _cost(adj, D) != 0:
            adj[u].add(v)
            adj[v].add(u)
    return [(a, b) for a in range(n) for b in adj[a] if a < b]


def _prune_regrow(n, edges, d, D, deadline, rng, consider):
    """Repeatedly prune redundant edges, regrow with cover vertices, keep the best."""
    best_n, best_e = n, list(edges)
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        pe = _prune_redundant(cur_n, cur_e, D, rng, deadline, 160)
        n2, e2 = _grow(cur_n, pe, d, D, deadline, rng)
        consider(n2, e2)
        if n2 > best_n:
            best_n, best_e = n2, list(e2)
        if n2 >= cur_n - 1:
            cur_n, cur_e = n2, list(e2)
        elif n2 < best_n - 2 or rng.random() < 0.3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Repair with pruning between additions.
#
# After each successful vertex addition, redundant edges are pruned. This frees
# degree on the current graph, so the next added vertex has more room to attach
# before annealing has to repair the diameter. Pruning keeps the diameter bound,
# so the state stays valid throughout.
# ----------------------------------------------------------------------------

def _repair(d, D, n, edges, deadline, rng, consider):
    """Repeatedly try to add one vertex to the current valid graph, repairing with annealing."""
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        side = rng.randrange(2)
        _add_vertex(adj, color, d, D, side, rng)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 1500, deadline):
            m = len(adj)
            e = [(u, v) for u in range(m) for v in adj[u] if u < v]
            consider(m, e)
            pe = _prune_redundant(m, e, D, rng, deadline, 200)
            adj = _to_sets(m, pe)
            color = _bipartition(m, adj)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    # Structured bases: generalized quadrangle for D >= 4, projective plane for D = 3.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            grow_end = start + 0.2 * time_limit
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)

    # New construction: voltage lifts of small bases over groups (Z_m x| Z_k).
    if D >= 2 and time.monotonic() < deadline:
        _voltage_stage(d, D, lambda: best_n, start + 0.45 * time_limit, rng, consider)

    # Randomized twin-duplication pipelines from the structured base (short).
    if D >= 2:
        trial_end = start + 0.50 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Kill-repair-regrow search from the best valid graph found so far (main improver).
    if D >= 2 and time.monotonic() < deadline:
        lns_end = start + 0.70 * time_limit
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    # Prune redundant edges to free degree, then regrow from the best graph.
    if D >= 2 and time.monotonic() < deadline:
        prune_end = start + 0.80 * time_limit
        _prune_regrow(best_n, best_e, d, D, prune_end, rng, consider)

    # Bold stage: repeated add-and-repair (with pruning) from the best valid graph.
    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best_n, best_e, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
