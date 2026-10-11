import itertools
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


# ----------------------------------------------------------------------------
# Greedy chord placement by exact bad-pair reduction.
#
# Adding an edge never increases the number of bad pairs (distances only shrink),
# so a chord between two deficient opposite-side vertices is always safe for the
# diameter. Random chords (_fill) waste spare degree. Here, a sample of candidate
# deficient pairs is scored by the exact bad-pair count after the chord, and the
# best one is kept.
# ----------------------------------------------------------------------------

def _greedy_chords(adj, color, d, D, rng, deadline, steps=12, sample=10):
    """Add cross-side chords that most reduce bad pairs. Returns True if cost reaches 0."""
    cur = _cost(adj, D)
    for _ in range(steps):
        if cur == 0 or time.monotonic() > deadline:
            break
        n = len(adj)
        left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
        right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
        if not left or not right:
            break
        # Sample candidate pairs without building the full product when it is large.
        pairs = []
        for _try in range(sample * 4):
            a = rng.choice(left)
            b = rng.choice(right)
            if b not in adj[a] and (a, b) not in pairs:
                pairs.append((a, b))
                if len(pairs) >= sample:
                    break
        if not pairs:
            break
        best, best_c = None, None
        for a, b in pairs:
            adj[a].add(b)
            adj[b].add(a)
            c = _cost(adj, D)
            adj[a].discard(b)
            adj[b].discard(a)
            if best_c is None or c < best_c:
                best, best_c = (a, b), c
        a, b = best
        adj[a].add(b)
        adj[b].add(a)
        cur = best_c
    return cur == 0


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


def _local_kill(n, edges, k, rng):
    """Pick k vertices forming a connected-ish cluster: a random vertex plus its nearby vertices.

    Killing a cluster frees a whole region of spare degree at once, so the regrow
    step can re-fill it with a different local structure. Falls back to random
    vertices if the cluster cannot grow (isolated start).
    """
    adj = _to_sets(n, edges)
    v = rng.randrange(n)
    kill = {v}
    frontier = [v]
    while len(kill) < k and frontier:
        x = frontier.pop(rng.randrange(len(frontier)))
        nbrs = list(adj[x])
        rng.shuffle(nbrs)
        for y in nbrs:
            if len(kill) >= k:
                break
            if y not in kill:
                kill.add(y)
                frontier.append(y)
    while len(kill) < k:
        kill.add(rng.randrange(n))
    return kill


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
        if k >= cur_n:
            break
        # Mix local (clustered) kills with uniformly random kills.
        if rng.random() < 0.6:
            kill = _local_kill(cur_n, cur_e, k, rng)
        else:
            kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        if rng.random() < 0.25:
            _greedy_chords(adj, color, d, D, rng, deadline, steps=8, sample=8)
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
# Cross-matching doubling with annealed repair.
#
# Take two copies A and B of a valid base graph G (n vertices, max degree d).
# Each vertex v has spare = d - deg(v). Within each copy, edges stay as they are.
# Spare stubs are joined across the copies: an A-vertex of colour c is matched to
# a B-copy of a vertex of colour 1 - c. Because the copy has the same colouring,
# every cross edge joins opposite colours, so the result is bipartite, degrees
# stay <= d, and every vertex keeps its own spare quota in each role. The 2n-vertex
# graph is then repaired with degree-preserving bipartite switches (the same
# annealer as LNS), accepted only at zero bad pairs. The Moore bound is checked
# first, so no hopeless attempt is made.
# ----------------------------------------------------------------------------

def _double_cross(n, edges, d, D, rng, deadline):
    """Try to build a valid 2n-vertex graph from two cross-matched copies of a base graph.

    Returns (N, edges) when the repaired graph has zero bad pairs, else None.
    """
    N = 2 * n
    if N > lib.moore_bound(d, D):
        return None
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    B = [set() for _ in range(N)]
    for u in range(n):
        for v in adj[u]:
            B[u].add(v)
            B[u + n].add(v + n)
    spare = [d - len(adj[v]) for v in range(n)]
    s0 = [v for v in range(n) if color[v] == 0 for _ in range(spare[v])]
    s1 = [v for v in range(n) if color[v] == 1 for _ in range(spare[v])]
    rng.shuffle(s0)
    rng.shuffle(s1)
    t0 = list(s0)
    t1 = list(s1)
    rng.shuffle(t0)
    rng.shuffle(t1)
    # Matching 1: A colour-0 stubs with B colour-1 copies.
    for x, w in zip(s0, s1):
        y = w + n
        if y not in B[x] and len(B[x]) < d and len(B[y]) < d:
            B[x].add(y)
            B[y].add(x)
    # Matching 2: A colour-1 stubs with B colour-0 copies.
    for x, w in zip(t1, t0):
        y = w + n
        if y not in B[x] and len(B[x]) < d and len(B[y]) < d:
            B[x].add(y)
            B[y].add(x)
    color2 = color + [1 - c for c in color]
    _fill(B, color2, d, rng)
    while time.monotonic() < deadline:
        if _anneal(B, color2, d, D, rng, 3000, deadline):
            return N, [(u, v) for u in range(N) for v in B[u] if u < v]
        # Restart the annealer from a fresh cross matching.
        return None
    return None


def _try_doubling(n, edges, d, D, deadline, rng, consider):
    """Repeatedly attempt cross-matching doubling of the base until the deadline."""
    while time.monotonic() < deadline:
        res = _double_cross(n, edges, d, D, rng, deadline)
        if res is not None:
            N, e = res
            consider(N, e)
            return True
    return False


# ----------------------------------------------------------------------------
# Vertex splitting with neighbour partition, then annealed repair.
#
# Pick a vertex v with at least two neighbours and split it into v and a new
# twin-like vertex w on the same side. The neighbours of v are partitioned at
# random: S1 stays joined to v, S2 is moved to w. Every neighbour keeps exactly
# one edge into {v, w}, so its degree is unchanged, and v and w each have degree
# at most deg(v) <= d. Distances can grow, because v and w no longer share their
# neighbourhood. Spare degree is then used by _fill, and degree-preserving
# switches repair the diameter. A split is kept only at zero bad pairs, so the
# walk stays on valid graphs and each success adds one vertex.
# ----------------------------------------------------------------------------

def _split_repair(n, edges, d, D, deadline, rng, consider):
    """Repeatedly split a random vertex of the current valid graph and repair it."""
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        cur_n = len(adj)
        cands = [v for v in range(cur_n) if len(adj[v]) >= 2]
        if not cands:
            break
        v = rng.choice(cands)
        nb = list(adj[v])
        rng.shuffle(nb)
        k = rng.randint(1, len(nb) - 1)
        S1, S2 = nb[:k], nb[k:]
        w = cur_n
        adj.append(set(S2))
        color.append(color[v])
        adj[v] = set(S1)
        for u in S2:
            adj[u].discard(v)
            adj[u].add(w)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 1500, deadline):
            m = len(adj)
            e = [(a, b) for a in range(m) for b in adj[a] if a < b]
            consider(m, e)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


def _prune_then_split(n, edges, d, D, deadline, rng, consider):
    """Prune redundant edges first (frees degree), then run split-repair from the result."""
    if time.monotonic() >= deadline:
        return
    pe = _prune_redundant(n, edges, D, rng, deadline, 160)
    n2, e2 = _grow(n, pe, d, D, deadline, rng)
    consider(n2, e2)
    _split_repair(n2, e2, d, D, deadline, rng, consider)


# ----------------------------------------------------------------------------
# Repair with an added vertex.
#
# Each attempt adds one vertex to the current valid graph. The new vertex's
# spare slots are filled either by greedy exact chords or random cross
# edges, then degree-preserving switches repair the diameter. Success is only
# accepted at zero bad pairs.
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
        if rng.random() < 0.5:
            _greedy_chords(adj, color, d, D, rng, deadline)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 1500, deadline):
            m = len(adj)
            e = [(u, v) for u in range(m) for v in adj[u] if u < v]
            consider(m, e)
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

    # Cross-matching doubling of the best base that fits under the Moore bound.
    if D >= 2 and 2 * base_n <= lib.moore_bound(d, D):
        dbl_end = start + 0.20 * time_limit
        _try_doubling(base_n, base_e, d, D, dbl_end, rng, consider)

    # Randomized twin-duplication pipelines from the structured base (short, cheap).
    if D >= 2:
        trial_end = start + 0.10 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Kill-repair-regrow search from the best valid graph found so far (main improver).
    if D >= 2 and time.monotonic() < deadline:
        lns_end = start + 0.50 * time_limit
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    # Prune redundant edges to free degree, then regrow from the best graph.
    if D >= 2 and time.monotonic() < deadline:
        prune_end = start + 0.66 * time_limit
        _prune_regrow(best_n, best_e, d, D, prune_end, rng, consider)

    # Prune, regrow, then split vertices and repair the diameter.
    if D >= 2 and time.monotonic() < deadline:
        split_end = start + 0.79 * time_limit
        _prune_then_split(best_n, best_e, d, D, split_end, rng, consider)

    # Bold stage: repeated add-and-repair from the largest valid graph found so far.
    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best_n, best_e, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
