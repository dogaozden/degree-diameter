"""Construction program for bipartite graphs with max degree d and diameter D.

Families: projective-plane incidence graphs, Araujo-Pardo & Lopez extensions,
generalized quadrangles (D >= 4), arc-extended projective planes, and a
randomized rewire search for D = 3.

New in this version: "overgrow and prune". For D = 3, the best valid graph is
enlarged past its diameter bound by attaching extra vertices with a greedy
max-coverage rule. Vertices with the most bad pairs are then deleted one at a
time, with degree-restoring saturation after each deletion, until the graph
is valid again. The loop accepts the result only when it beats the current
order, so it can only grow the graph.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph utilities.
# ----------------------------------------------------------------------------

def _adj_list(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _saturate(n, edges, color, d, rng):
    """Randomly join deficient opposite-colour vertices, keeping degrees <= d."""
    edges = list(edges)
    deg = [0] * n
    existing = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        existing.add((min(u, v), max(u, v)))
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d and (min(a, b), max(a, b)) not in existing:
            edges.append((a, b))
            existing.add((min(a, b), max(a, b)))
            deg[a] += 1
            deg[b] += 1
    return edges


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
    adj = _adj_list(n, edges)
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


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices first, then saturate edges with the leftover spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        adj = _adj_list(cur_n, e2)
        cur_e = _saturate(cur_n, e2, _bipartition(cur_n, adj), d, rng)
        if not grew:
            break
    return cur_n, cur_e


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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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


def _local_improve(m, s, point_lines, line_points, S, rng, deadline, iters):
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m

    def add(P):
        inS[P] = True
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def rem(P):
        inS[P] = False
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def fits(P):
        return (all(cl[L] < s for L in point_lines[P])
                and all(cp[Q] < s for Q in line_points[P]))

    cur = list(S)
    for P in cur:
        add(P)
    best = list(cur)
    for it in range(iters):
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        if fits(P):
            add(P)
            cur.append(P)
            if len(cur) > len(best):
                best = list(cur)
            continue
        if not cur:
            continue
        idx = rng.randrange(len(cur))
        R = cur[idx]
        rem(R)
        if fits(P):
            add(P)
            cur[idx] = P
        else:
            add(R)
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
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
            g = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
            g = _local_improve(m, s, point_lines, line_points, g, rng, deadline, 3000)
            cands.append(g)
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
# NEW: overgrow and prune for diameter 3.
# ----------------------------------------------------------------------------

def _max_cover(cands, ball, d, rng):
    """Pick up to d candidates greedily maximizing newly covered vertices (with some noise)."""
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while pool and len(chosen) < d:
        if rng.random() < 0.15:
            best = pool[rng.randrange(len(pool))]
        else:
            best, bg = None, -1
            for s in pool:
                g = (ball[s] & ~covered).bit_count()
                if g > bg:
                    bg, best = g, s
        pool.remove(best)
        chosen.append(best)
        covered |= ball[best]
    return chosen


def _overgrow(n, edges, color, d, D, extra, rng, deadline):
    """Attach `extra` new vertices by max-cover, ignoring the diameter constraint."""
    edges = list(edges)
    color = list(color)
    adj = _adj_list(n, edges)
    deg = [len(a) for a in adj]
    for t in range(extra):
        if time.monotonic() > deadline:
            break
        ball = _balls_radius(n, adj, D - 1)
        c = t % 2
        cands = [s for s in range(n) if color[s] == c and deg[s] < d]
        if not cands:
            c = 1 - c
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                break
        chosen = _max_cover(cands, ball, d, rng)
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
    return n, edges, color


def _prune(n, edges, color, d, D, deadline, rng):
    """Repeatedly delete a worst vertex and resaturate, until diameter <= D. None on failure."""
    edges = list(edges)
    color = list(color)
    while True:
        if time.monotonic() > deadline or n < 2:
            return None
        adj = _adj_list(n, edges)
        balls = _balls_radius(n, adj, D)
        bad = [n - b.bit_count() for b in balls]
        if sum(bad) == 0:
            return n, edges, color
        mx = max(bad)
        r = rng.choice([v for v in range(n) if bad[v] == mx])
        keep = [v for v in range(n) if v != r]
        mp = {old: i for i, old in enumerate(keep)}
        edges = [(mp[u], mp[v]) for u, v in edges if u != r and v != r]
        color = [color[v] for v in keep]
        n -= 1
        edges = _saturate(n, edges, color, d, rng)


def _search_prune(n, edges, d, D, deadline, rng, on_valid):
    """Overgrow the current valid graph by a few percent, prune back, keep if larger."""
    cur_n, cur_e = n, list(edges)
    color = _bipartition(cur_n, _adj_list(cur_n, cur_e))
    while time.monotonic() < deadline:
        extra = max(2, int(rng.uniform(0.02, 0.15) * cur_n))
        gn, ge, gc = _overgrow(cur_n, cur_e, color, d, D, extra, rng, deadline)
        res = _prune(gn, ge, gc, d, D, deadline, rng)
        if res is None:
            continue
        pn, pe, pc = res
        if pn > cur_n:
            cur_n, cur_e, color = pn, pe, pc
            on_valid(pn, pe)
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Matching-rewire growth for diameter 3.
# ----------------------------------------------------------------------------

def _random_matching(Eo, d, rng):
    pool = list(Eo)
    rng.shuffle(pool)
    used = set()
    R = []
    for u, v in pool:
        if u in used or v in used:
            continue
        R.append((u, v))
        used.add(u)
        used.add(v)
        if len(R) == d:
            return R
    return None


def _rewire_build(n, Eo_set, R):
    Rkeys = {(min(u, v), max(u, v)) for u, v in R}
    out = [e for e in Eo_set if (min(e[0], e[1]), max(e[0], e[1])) not in Rkeys]
    x, y = n, n + 1
    for u, v in R:
        out.append((x, v))
        out.append((u, y))
    return n + 2, out


def _pair_search(n, E, d, D, deadline, rng):
    adj = _adj_list(n, E)
    col = _bipartition(n, adj)
    if any(col[u] == col[v] for u, v in E):
        return None
    Eo = [(u, v) if col[u] == 0 else (v, u) for u, v in E]
    if len(Eo) < d:
        return None
    R = _random_matching(Eo, d, rng)
    if R is None:
        return None

    def cost(RR):
        nn, ee = _rewire_build(n, Eo, RR)
        return lib.bad_pairs(nn, ee, D)

    c = cost(R)
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)
    while time.monotonic() < deadline:
        if c == 0:
            return _rewire_build(n, Eo, R)
        frac = (time.monotonic() - t_start) / span
        T = 1.0 * (0.05 ** frac)
        i = rng.randrange(d)
        cand = Eo[rng.randrange(len(Eo))]
        used = set()
        for j, (a, b) in enumerate(R):
            if j != i:
                used.add(a)
                used.add(b)
        if cand[0] in used or cand[1] in used:
            continue
        newR = list(R)
        newR[i] = cand
        c2 = cost(newR)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            R, c = newR, c2
    if c == 0:
        return _rewire_build(n, Eo, R)
    return None


def _pair_grow(n, E, d, D, deadline, rng):
    cur_n, cur_e = n, list(E)
    while time.monotonic() < deadline:
        res = _pair_search(cur_n, cur_e, d, D, deadline, rng)
        if res is None:
            break
        cur_n, cur_e = res
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    if D >= 3:
        # Araujo-Pardo & Lopez record family for d = q + 2 with q a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                consider(n_a, e_a)
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.15 * time_limit, rng)
            consider(n2, e2)
        for n_c, e_c in _arc_extensions(d, start + 0.25 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.6 * time_limit, rng)
            consider(n2, e2)

    if D == 3:
        # NEW: overgrow the best valid graph and prune back to diameter 3.
        _search_prune(best[0], best[1], d, D, start + 0.7 * time_limit,
                      random.Random(seed + 17), consider)
        # Matching-rewire growth from the best graph found so far.
        n3, e3 = _pair_grow(best[0], best[1], d, D,
                            start + 0.88 * time_limit, random.Random(seed + 101))
        consider(n3, e3)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
