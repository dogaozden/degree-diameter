import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Known bases: Araujo-Pardo-Lopez, projective plane, generalized quadrangle.
# ----------------------------------------------------------------------------

def _araujo_best(d):
    """Araujo-Pardo-Lopez graph for the largest prime power q <= d - 2 (degree q + 2 <= d, diameter 3)."""
    for q in range(min(d - 2, 23), 2, -1):
        if lib.is_prime_power(q):
            try:
                return lib.araujo_lopez_graph(q)
            except ValueError:
                return None
    return None


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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Cover-based vertex extension and edge saturation (diameter-preserving growth).
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the graph."""
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
    """Greedily join deficient opposite-side vertices in random order."""
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
    """Extend by cover vertices first, then saturate edges with the leftover spare degree."""
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
# Plateau walk by vertex re-homing, with growth.
# ----------------------------------------------------------------------------

def _plateau_walk(n, edges, d, D, deadline, rng):
    """Return the largest valid (n, edges) found by re-homing walks starting from (n, edges)."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        adj = [set() for _ in range(cur_n)]
        for u, v in cur_e:
            adj[u].add(v)
            adj[v].add(u)
        color = _bipartition(cur_n, [list(s) for s in adj])
        for _ in range(40):
            if time.monotonic() >= deadline:
                break
            v = rng.randrange(cur_n)
            old = list(adj[v])
            for u in old:
                adj[u].discard(v)
            adj[v] = set()
            opp = 1 - color[v]
            cands = [s for s in range(cur_n) if color[s] == opp and len(adj[s]) < d]
            ball = _balls_radius(cur_n, adj, D - 1)
            full = ((1 << cur_n) - 1) & ~(1 << v)
            chosen = _greedy_cover(cands, ball, full, d, rng, True)
            accepted = False
            if chosen:
                for s in chosen:
                    adj[s].add(v)
                    adj[v].add(s)
                E = [(a, b) for a in range(cur_n) for b in adj[a] if a < b]
                if lib.is_valid(cur_n, E, d, D):
                    accepted = True
            if not accepted:
                if chosen:
                    for s in chosen:
                        adj[s].discard(v)
                        adj[v].discard(s)
                for u in old:
                    adj[u].add(v)
                adj[v] = set(old)
        cur_e = [(a, b) for a in range(cur_n) for b in adj[a] if a < b]
        if time.monotonic() < deadline:
            gn, ge = _grow(cur_n, cur_e, d, D, deadline, rng)
            if gn > cur_n and lib.is_valid(gn, ge, d, D):
                cur_n, cur_e = gn, ge
        if cur_n > best_n:
            best_n, best_e = cur_n, list(cur_e)
    return best_n, best_e


# ----------------------------------------------------------------------------
# NEW: greedy vertex-deletion repair of an oversized random lift.
#
# Build a bi-Cayley lift with random voltages whose order is somewhat above
# the current best. Such a lift has degree <= d and is bipartite, but its
# diameter is too large. Repeatedly delete the vertices that sit in the most
# bad pairs (pairs at distance > D, counted with bitmasks), until no bad pair
# remains. Deleting vertices keeps degree and bipartiteness, so the result is
# a candidate for a larger valid graph than the current best. Then grow it.
# ----------------------------------------------------------------------------

def _random_lift(d, k, G, mul, rng):
    """Random bi-Cayley lift: k vertices per side, d layers, each layer a permutation of B."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append((i, k + p[i], rng.randrange(G)))
    return lib.group_lift(2 * k, darts, G, mul)


def _delete_repair(n, edges, D, deadline, rng):
    """Greedily delete high-badness vertices until the graph has diameter <= D; None on failure."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    alive = [True] * n
    n_alive = n
    while True:
        if time.monotonic() >= deadline or n_alive < 2:
            return None
        ball = [(1 << v) if alive[v] else 0 for v in range(n)]
        for _ in range(D):
            new = [0] * n
            for v in range(n):
                if alive[v]:
                    x = ball[v]
                    for u in adj[v]:
                        x |= ball[u]
                    new[v] = x
            ball = new
        bad = {}
        for v in range(n):
            if alive[v]:
                b = n_alive - ball[v].bit_count()
                if b:
                    bad[v] = b
        if not bad:
            break
        order = sorted(bad, key=lambda v: (-bad[v], rng.random()))
        batch = order[:max(1, n_alive // 100)]
        for v in batch:
            alive[v] = False
            n_alive -= 1
            for u in adj[v]:
                adj[u].discard(v)
            adj[v] = set()
    out = [(u, v) for u in range(n) if alive[u] for v in adj[u] if u < v]
    return lib.relabel(out)


def _sample_group_rng(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    return _sample_group(G, rng)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3 and best_n < moore:
        # Araujo-Pardo-Lopez record base (degree q + 2 <= d), grown if possible.
        ara = _araujo_best(d)
        if ara is not None:
            consider(ara[0], ara[1])
            n2, e2 = _grow(ara[0], ara[1], d, D, start + 0.15 * time_limit,
                           random.Random(seed + 2))
            consider(n2, e2)
        # Plain projective plane, grown by cover extension and saturation.
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.25 * time_limit,
                           random.Random(seed + 1))
            consider(n2, e2)
        # Arc-extended projective plane graphs.
        for n_c, e_c in _arc_extensions(d, start + 0.35 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4 and best_n < moore and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.4 * time_limit, rng)
            consider(n2, e2)

    # Plateau walk on the best valid graph so far, for a bounded share of time.
    if D >= 3 and best_n < moore and time.monotonic() < deadline:
        frac = 0.25 if D <= 4 else 0.10
        walk_end = min(deadline, start + frac * time_limit)
        wn, we = _plateau_walk(best[0], best[1], d, D, walk_end,
                               random.Random(seed + 11))
        consider(wn, we)

    # Main search loop: deletion repair of oversized random lifts, annealed
    # group voltage lifts, and Haar attempts for small D.
    ks = [1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    haar_m, haar_miss = d + 1, 0
    fails = 0
    while time.monotonic() < deadline and best_n < moore:
        if D <= 4 and haar_miss < 4 and rng.random() < 0.1:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
            continue

        k = rng.choice(ks)
        base = best_n // (2 * k)

        # NEW: oversized random lift, repaired by greedy vertex deletion.
        if rng.random() < 0.25:
            G = max(2, int(base * (1.10 + 0.25 * rng.random())) + 1)
            g = _sample_group_rng(G, rng)
            if g is None:
                fails += 1
                continue
            order, mul = g
            n0, e0 = _random_lift(d, k, order, mul, rng)
            rep_end = min(deadline, time.monotonic() + 2.5)
            rep = _delete_repair(n0, e0, D, rep_end, rng)
            if rep is not None:
                rn, re_ = rep
                consider(rn, re_)
                if rn > best_n:
                    gn, ge = _grow(best[0], best[1], d, D,
                                   min(deadline, time.monotonic() + 1.0),
                                   random.Random(seed + fails))
                    consider(gn, ge)
            continue

        spread = min(0.6, 0.04 * (1 + fails))
        hi = max(base // 8 + 1, int(base * spread))
        G = max(2, base + 1 + rng.randrange(0, hi))
        g = _sample_group(G, rng)
        if g is None:
            fails += 1
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline,
                      run_secs=3.0, iters=400)
        if res is not None:
            consider(res[0], res[1])
            fails = 0
        else:
            fails += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
