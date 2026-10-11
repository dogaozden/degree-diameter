import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
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
    """W(q) incidence graph for the largest prime power q <= 9 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
# ----------------------------------------------------------------------------

class _Best:
    """Holds the best valid graph found so far."""

    def __init__(self, d, D, n, e):
        self.d = d
        self.D = D
        self.n = n
        self.e = list(e)

    def consider(self, n, e):
        if n > self.n and lib.is_valid(n, e, self.d, self.D):
            self.n = n
            self.e = list(e)


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


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of deficient ones."""
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
            for attempt in range(attempts):
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
    """Greedily join deficient opposite-side vertices in random order (only shortens distances)."""
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


def _grow(n, edges, d, D, deadline, rng, attempts=200):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, attempts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Twin duplication (non-adjacent twins keep distances and bipartiteness).
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
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    return n, e


# ----------------------------------------------------------------------------
# Bipartite annealing, shared by the lift stages, LNS and repair.
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


# ----------------------------------------------------------------------------
# Group lifts over Z_m x| Z_k (left translation is an automorphism, so one BFS
# per base vertex checks the diameter).
# ----------------------------------------------------------------------------

def _groups_of_order(G):
    """All (m, k, r) with m*k = G giving a semidirect product Z_m x| Z_k."""
    out = []
    for m in range(1, G + 1):
        if G % m:
            continue
        k = G // m
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _lift_cost(kb, G, T, d, D, tgt, lab):
    """Sum over base vertices of lifted vertices not reached within D of (u, identity)."""
    n = 2 * kb * G
    nbr = [[] for _ in range(n)]
    for t in range(d):
        tt = tgt[t]
        lt = lab[t]
        for i in range(kb):
            j = kb + tt[i]
            g = lt[i]
            for x in range(G):
                a = i * G + x
                b = j * G + T[x][g]
                nbr[a].append(b)
                nbr[b].append(a)
    total = 0
    for u in range(2 * kb):
        s = u * G
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                for w in nbr[v]:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += n - cnt
    return total


def _group_lift_search(kb, G, T, d, D, deadline, rng):
    """Anneal dart labels and slot permutations until the lift has diameter <= D. Returns (n, edges) or None."""
    n = 2 * kb * G
    tgt = []
    lab = []
    for _ in range(d):
        p = list(range(kb))
        rng.shuffle(p)
        tgt.append(p)
        lab.append([rng.randrange(G) for _ in range(kb)])
    cur = _lift_cost(kb, G, T, d, D, tgt, lab)
    temp = 2.0
    while cur > 0 and time.monotonic() < deadline:
        if kb >= 2 and rng.random() < 0.3:
            t = rng.randrange(d)
            i1, i2 = rng.sample(range(kb), 2)
            tt = tgt[t]
            tt[i1], tt[i2] = tt[i2], tt[i1]
            c = _lift_cost(kb, G, T, d, D, tgt, lab)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                tt[i1], tt[i2] = tt[i2], tt[i1]
        else:
            t = rng.randrange(d)
            i = rng.randrange(kb)
            old = lab[t][i]
            new = rng.randrange(G)
            if new == old:
                continue
            lab[t][i] = new
            c = _lift_cost(kb, G, T, d, D, tgt, lab)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                lab[t][i] = old
    if cur != 0:
        return None
    edges = set()
    for t in range(d):
        for i in range(kb):
            j = kb + tgt[t][i]
            g = lab[t][i]
            for x in range(G):
                edges.add((i * G + x, j * G + T[x][g]))
    return n, sorted(edges)


def _group_stage(best, rng, deadline):
    """Ladder over group-lift sizes above best.n; each success updates best."""
    d, D = best.d, best.D
    limit_n = min(lib.moore_bound(d, D), 1200)
    cands = []
    for kb in range(1, 7):
        for G in range(best.n // (2 * kb) + 1, limit_n // (2 * kb) + 1):
            n = 2 * kb * G
            if best.n < n <= limit_n:
                cands.append((n, kb, G))
    cands.sort()
    for n, kb, G in cands:
        if time.monotonic() >= deadline:
            break
        if n <= best.n:
            continue
        groups = _groups_of_order(G)
        if not groups:
            continue
        m, k, r = rng.choice(groups)
        try:
            order, mul, _ = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        T = [[mul(x, g) for g in range(order)] for x in range(order)]
        slice_end = min(deadline, time.monotonic() + 4.0)
        res = _group_lift_search(kb, G, T, d, D, slice_end, rng)
        if res is not None:
            best.consider(res[0], res[1])


# ----------------------------------------------------------------------------
# Random voltage lifts of small d-regular bipartite base multigraphs, repaired
# with annealing and grown.
# ----------------------------------------------------------------------------

def _random_lift(k, m, d, rng):
    """Random Z_m lift of a d-regular bipartite multigraph on k + k base vertices."""
    darts = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            darts.append((i, k + perm[i], rng.randrange(m)))
    return lib.voltage_lift(2 * k, darts, m)


def _voltage_stage(best, rng, deadline):
    """Search random voltage lifts slightly above best.n, repair, then grow."""
    d, D = best.d, best.D
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        if best.n >= moore:
            return
        k = rng.choice((1, 1, 2, 3))
        target = min(moore, best.n + rng.randint(1, 12))
        m = -(-target // (2 * k))
        if 2 * k * m > moore:
            m = moore // (2 * k)
        if m < 2 or 2 * k * m <= best.n:
            continue
        n, e = _random_lift(k, m, d, rng)
        adj = _to_sets(n, e)
        color = [0 if v < k * m else 1 for v in range(n)]
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(n) for v in adj[u] if u < v]
        best.consider(n, e3)
        n4, e4 = _grow(n, e3, d, D, deadline, rng, attempts=30)
        best.consider(n4, e4)


# ----------------------------------------------------------------------------
# Kill-repair-regrow LNS, anchored to the best graph.
# ----------------------------------------------------------------------------

def _lns(n, edges, d, D, deadline, rng, consider):
    """Delete 1-3 vertices, repair the diameter by switches, regrow; anchored to the best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 3))
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
        n4, e4 = _grow(m, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


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
        else:
            adj[:] = snap_adj
            color[:] = snap_color


# ----------------------------------------------------------------------------
# Driver. Stage windows as fractions of time_limit:
#   structured base + growth   -> 0.15
#   twin trials                -> 0.25
#   group lifts (D >= 3)       -> 0.38
#   voltage lifts              -> 0.48
#   LNS                        -> 0.72
#   repair                     -> 0.85
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    rng = random.Random(seed)
    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2
    best = _Best(d, D, fallback[0], fallback[1])
    moore = lib.moore_bound(d, D)

    def at(frac):
        return start + frac * time_limit

    def done():
        return best.n >= moore

    def result():
        if not lib.is_valid(best.n, best.e, d, D):
            return fallback
        return best.n, list(best.e)

    if done():
        return result()

    base_n, base_e = best.n, list(best.e)
    try:
        if D >= 3:
            base = _best_gq(d) if D >= 4 else None
            if base is None:
                base = _best_pg(d)
            if base is not None:
                best.consider(base[0], base[1])
                base_n, base_e = base[0], list(base[1])
                n1, e1 = _grow(base_n, base_e, d, D, at(0.15), rng)
                best.consider(n1, e1)
    except Exception:
        pass
    if done():
        return result()

    try:
        while time.monotonic() < at(0.25):
            n, e = _trial(base_n, base_e, d, D, rng, at(0.25))
            best.consider(n, e)
    except Exception:
        pass
    if done():
        return result()

    try:
        if D >= 3 and time.monotonic() < at(0.38):
            _group_stage(best, rng, at(0.38))
    except Exception:
        pass
    if done():
        return result()

    try:
        if time.monotonic() < at(0.48):
            _voltage_stage(best, rng, at(0.48))
    except Exception:
        pass
    if done():
        return result()

    try:
        if time.monotonic() < at(0.72):
            _lns(best.n, best.e, d, D, at(0.72), rng, best.consider)
    except Exception:
        pass
    if done():
        return result()

    try:
        if time.monotonic() < at(0.85):
            _repair(d, D, best.n, best.e, at(0.85), rng, best.consider)
    except Exception:
        pass

    return result()
