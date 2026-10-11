import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: projective plane (D = 3) and generalized quadrangle W(q) (D = 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q); bipartite, diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d (capped at 9 for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers. Adjacency is a list of neighbour containers (lists or sets).
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


def _all_within(n, adj, D):
    """True if every pair of vertices is within distance D."""
    full = (1 << n) - 1
    return all(b == full for b in _balls_radius(n, adj, D))


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency containers."""
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


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving growth). Used for the parents.
# ----------------------------------------------------------------------------

def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate balls; None if it fails."""
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


def _cover_ls(cands, ball, full, d, rng, steps, deadline):
    """Swap-based local search for a cover of `full` by k = min(d, |cands|) candidate balls."""
    if not cands:
        return None
    k = min(d, len(cands))
    S = rng.sample(cands, k)
    in_s = set(S)

    def union(sel):
        u = 0
        for s in sel:
            u |= ball[s]
        return u

    cost = (full & ~union(S)).bit_count()
    for step in range(steps):
        if cost == 0:
            break
        if (step & 255) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        rest = S[:i] + S[i + 1:]
        miss = full & ~union(rest)
        best_t, best_g = None, -1
        for t in rng.sample(cands, min(30, len(cands))):
            if t in in_s:
                continue
            g = (ball[t] & miss).bit_count()
            if g > best_g:
                best_t, best_g = t, g
        if best_t is None:
            continue
        newcost = (miss & ~ball[best_t]).bit_count()
        if newcost <= cost or rng.random() < 0.02:
            in_s.discard(S[i])
            S[i] = best_t
            in_s.add(best_t)
            cost = newcost
    return S if cost == 0 else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover everything within distance D-1 of the graph."""
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
            for attempt in range(25):
                if time.monotonic() >= deadline:
                    break
                if attempt < 5:
                    chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                else:
                    chosen = _cover_ls(cands, ball, full, d, rng, 2000, deadline)
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
    """Greedily join deficient opposite-side vertices in random order (keeps bipartiteness)."""
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
    """Alternate cover-vertex extension with saturation of leftover spare degree."""
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
# Bold branch: pair insertion by edge stealing.
#
# Insert two new vertices v (colour c) and w (colour 1-c) joined to each other.
# Pick d-1 existing edges (u_i, x_i) with u_i on side 1-c and x_i on side c, all
# endpoints distinct. Remove each such edge and join v to u_i and w to x_i.
# Every old vertex keeps its degree, v and w get degree d, and the bipartition
# is preserved. The insertion is kept only if the result still has diameter <= D.
# ----------------------------------------------------------------------------

def _pair_insertion(n, edges, d, D, deadline, rng):
    """Repeatedly grow a valid graph by pair insertion; return the largest valid (n, edges) found."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    colour = _bipartition(n, adj)
    moore = lib._moore_bound(d, D)

    while time.monotonic() < deadline and n + 2 <= moore:
        c = rng.randrange(2)
        cand = [(u, x) for u in range(n) if colour[u] == 1 - c for x in adj[u] if colour[x] == c]
        if len(cand) < d - 1:
            break
        rng.shuffle(cand)
        used_u, used_x, chosen = set(), set(), []
        for u, x in cand:
            if u in used_u or x in used_x:
                continue
            used_u.add(u)
            used_x.add(x)
            chosen.append((u, x))
            if len(chosen) == d - 1:
                break
        if len(chosen) < d - 1:
            continue

        adj2 = [set(s) for s in adj]
        for u, x in chosen:
            adj2[u].discard(x)
            adj2[x].discard(u)
        v, w = n, n + 1
        adj2.append(set())
        adj2.append(set())
        for u, x in chosen:
            adj2[v].add(u)
            adj2[u].add(v)
            adj2[w].add(x)
            adj2[x].add(w)
        adj2[v].add(w)
        adj2[w].add(v)

        if max(len(s) for s in adj2) > d:
            continue
        if _all_within(n + 2, adj2, D):
            adj = adj2
            n += 2
            colour = colour + [c, 1 - c]

    out = []
    for u in range(n):
        for v in adj[u]:
            if u < v:
                out.append((u, v))
    return n, out


# ----------------------------------------------------------------------------
# Driver. Every candidate is checked with lib.is_valid before it can be kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = (fallback[0], [(int(u), int(v)) for u, v in fallback[1]])
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, [(int(u), int(v)) for u, v in e])
            best_n = n

    # Parent-style base constructions and growth (kept as the starting point).
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.2 * time_limit, rng)
            consider(n2, e2)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            t = 0
            grow_deadline = start + 0.3 * time_limit
            while time.monotonic() < grow_deadline and t < 4:
                n2, e2 = _grow(gq[0], gq[1], d, D, grow_deadline,
                               random.Random(seed * 131 + t))
                consider(n2, e2)
                t += 1

    # Bold branch: pair insertion by edge stealing, starting from the best valid graph.
    if D >= 3 and best_n >= 2:
        n2, e2 = _pair_insertion(best_n, best[1], d, D, start + 0.82 * time_limit, rng)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = (fallback[0], [(int(u), int(v)) for u, v in fallback[1]])
    return best
