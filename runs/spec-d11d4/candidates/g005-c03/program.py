import itertools
import math
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
# Shared graph utilities.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r (adj may be lists or sets)."""
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
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
# Twin cloning with spare-slot harvesting (diameter-preserving).
#
# A twin u' of u with N(u') = N(u) keeps bipartiteness, keeps degree, and
# satisfies d(u, u') = 2, while d(u', w) = d(u, w) for every other w.
# ----------------------------------------------------------------------------

def _clone_pass(n, edges, d, rng, deadline):
    """Greedily add twins of vertices whose neighbours all still have spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    order = list(range(n))
    rng.shuffle(order)
    for u in order:
        if time.monotonic() >= deadline:
            break
        nb = adj[u]
        if not nb or any(deg[y] >= d for y in nb):
            continue
        v = n
        n += 1
        color.append(color[u])
        adj.append(list(nb))
        deg.append(len(nb))
        for y in nb:
            adj[y].append(v)
            deg[y] += 1
            edges.append((y, v))
    return n, edges


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving growth).
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


def _grow(n, edges, d, D, deadline, rng, clone_first=True):
    """Alternate twin cloning, cover-vertex extension and saturation of leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        if clone_first:
            cur_n, cur_e = _clone_pass(cur_n, cur_e, d, rng, deadline)
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not clone_first:
            cur_n, cur_e = _clone_pass(cur_n, cur_e, d, rng, deadline)
        if cur_n == before:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW: switch-insertion with a diameter oracle.
#
# Works on a fixed-size bipartite graph, degrees <= d. Two moves:
#   * insertion: pick d random vertices T of one side. Each t in T that is full
#     gives up one random edge (t, w). A new vertex v on the other side is joined
#     to all of T. The move is kept only if the diameter stays <= D (checked
#     exactly with bitmasks). Degrees stay <= d and bipartiteness holds by design.
#   * double-edge swap: (a,b),(c,e) -> (a,e),(c,b) on one side pair, a
#     degree-preserving plateau move that reshapes the graph so later
#     insertions can succeed.
# Every kept state is valid, so the best snapshot is always a valid graph.
# ----------------------------------------------------------------------------

def _ok_sets(adj, n, D):
    """True if every pair of the n vertices (adjacency sets adj) is within distance D."""
    full = (1 << n) - 1
    return all(x == full for x in _balls_radius(n, adj, D))


def _edges_of(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _switch_phase(n, edges, d, D, deadline, rng):
    edges = _saturate_edges(n, edges, d, rng)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    if not _ok_sets(adj, n, D):
        return n, edges
    color = _bipartition(n, [list(s) for s in adj])
    side = [[v for v in range(n) if color[v] == 0],
            [v for v in range(n) if color[v] == 1]]
    best_n, best_e = n, edges

    while time.monotonic() < deadline:
        if rng.random() < 0.6:
            c = rng.randrange(2)
            if len(side[c]) < d:
                continue
            T = rng.sample(side[c], d)
            rem = [(t, rng.choice(list(adj[t]))) for t in T if len(adj[t]) >= d]
            for t, w in rem:
                adj[t].discard(w)
                adj[w].discard(t)
            v = n
            adj.append(set(T))
            for t in T:
                adj[t].add(v)
            n += 1
            if _ok_sets(adj, n, D):
                side[1 - c].append(v)
                best_n = n
                best_e = _edges_of(adj)
            else:
                for t in T:
                    adj[t].discard(v)
                adj.pop()
                n -= 1
                for t, w in rem:
                    adj[t].add(w)
                    adj[w].add(t)
        else:
            if not side[0] or not side[1]:
                continue
            a = rng.choice(side[0])
            if not adj[a]:
                continue
            b = rng.choice(list(adj[a]))
            c2 = rng.choice(side[0])
            if c2 == a or not adj[c2]:
                continue
            e2 = rng.choice(list(adj[c2]))
            if e2 in adj[a] or b in adj[c2]:
                continue
            adj[a].discard(b)
            adj[b].discard(a)
            adj[c2].discard(e2)
            adj[e2].discard(c2)
            adj[a].add(e2)
            adj[e2].add(a)
            adj[c2].add(b)
            adj[b].add(c2)
            if not _ok_sets(adj, n, D):
                adj[a].discard(e2)
                adj[e2].discard(a)
                adj[c2].discard(b)
                adj[b].discard(c2)
                adj[a].add(b)
                adj[b].add(a)
                adj[c2].add(e2)
                adj[e2].add(c2)
    return best_n, best_e


# ----------------------------------------------------------------------------
# Driver. Every candidate is checked with lib.is_valid before it can be kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    base = None
    if D == 3:
        base = _best_pg(d)
    elif D >= 4:
        base = _best_gq(d)

    if base is not None:
        consider(base[0], base[1])
        cur_n, cur_e = base[0], base[1]
        # Diameter-preserving growth from the algebraic base (clones, covers, saturation).
        g_n, g_e = _grow(cur_n, cur_e, d, D, start + 0.3 * tl, random.Random(seed * 7 + 1))
        if g_n > cur_n and lib.is_valid(g_n, g_e, d, D):
            cur_n, cur_e = g_n, g_e
        consider(cur_n, cur_e)
    else:
        cur_n, cur_e = best_n, best[1]

    # New: switch-insertion with exact diameter oracle, using the remaining budget.
    sw_n, sw_e = _switch_phase(cur_n, cur_e, d, D, start + 0.75 * tl, rng)
    consider(sw_n, sw_e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
