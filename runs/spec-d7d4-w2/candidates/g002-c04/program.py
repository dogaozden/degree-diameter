import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective planes (D = 3) and generalized quadrangles W(q) (D = 4).
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


# ----------------------------------------------------------------------------
# Shared utilities.
# ----------------------------------------------------------------------------

def _adj_list(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


# ----------------------------------------------------------------------------
# Twin augmentation by packing (add twins of a set of vertices, same neighbourhood).
# ----------------------------------------------------------------------------

def _twin_packing(n, adj, slack, rng, deadline):
    cand = [x for x in range(n) if adj[x] and all(slack[w] > 0 for w in adj[x])]
    if not cand:
        return []
    inset = [False] * n
    load = [0] * n

    def take(x):
        inset[x] = True
        for w in adj[x]:
            load[w] += 1

    def drop(x):
        inset[x] = False
        for w in adj[x]:
            load[w] -= 1

    def fill(order):
        for x in order:
            if not inset[x] and all(load[w] < slack[w] for w in adj[x]):
                take(x)

    order = cand[:]
    rng.shuffle(order)
    fill(order)
    best = [x for x in cand if inset[x]]
    while time.monotonic() < deadline:
        chosen = [x for x in cand if inset[x]]
        for x in rng.sample(chosen, min(rng.randint(1, 3), len(chosen))):
            drop(x)
        order = cand[:]
        rng.shuffle(order)
        fill(order)
        cur = sum(1 for x in cand if inset[x])
        if cur > len(best):
            best = [x for x in cand if inset[x]]
        elif cur < len(best) - 2 or rng.random() < 0.01:
            for x in cand:
                if inset[x]:
                    drop(x)
            for x in best:
                take(x)
    return best


def _twin_augment(n, edges, d, rng, deadline):
    adj = _adj_list(n, edges)
    slack = [max(0, d - len(a)) for a in adj]
    chosen = _twin_packing(n, adj, slack, rng, deadline)
    E = list(edges)
    N = n
    for x in chosen:
        for w in adj[x]:
            E.append((N, w))
        N += 1
    return N, E


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (D = 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
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
# Cover-based vertex extension (diameter-preserving) and edge saturation.
# ----------------------------------------------------------------------------

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


def _ls_cover(cands, ball, full, d, n, deadline, rng, steps):
    """Swap-based local search for a small covering set of at most d candidates."""
    if not cands or full == 0:
        return None
    cur = rng.sample(cands, min(d, len(cands)))

    def cover_of(sel):
        c = 0
        for s in sel:
            c |= ball[s]
        return c

    cur_unc = (full & ~cover_of(cur)).bit_count()
    for _ in range(steps):
        if cur_unc == 0:
            return cur
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(len(cur))
        rest = cur[:i] + cur[i + 1:]
        missing = full & ~cover_of(rest)
        if missing == 0:
            return rest
        while True:
            w = rng.randrange(n)
            if (missing >> w) & 1:
                break
        chosen_set = set(cur)
        opts = [s for s in cands if (ball[s] >> w) & 1 and s not in chosen_set]
        if not opts:
            continue
        new = rng.choice(opts)
        trial = rest + [new]
        u = (full & ~cover_of(trial)).bit_count()
        if u <= cur_unc or rng.random() < 0.02:
            cur = trial
            cur_unc = u
    return cur if cur_unc == 0 else None


def _exact_cover(cands, ball, full, d, budget):
    nodes = [0]

    def rec(covered, chosen):
        unc = full & ~covered
        if unc == 0:
            return chosen
        room = d - len(chosen)
        if room <= 0:
            return None
        nodes[0] += 1
        if nodes[0] > budget:
            return None
        gains = [(ball[s] & unc).bit_count() for s in cands]
        mx = max(gains, default=0)
        if mx == 0 or unc.bit_count() > room * mx:
            return None
        w = (unc & -unc).bit_length() - 1
        opts = [i for i, s in enumerate(cands) if gains[i] > 0 and (ball[s] >> w) & 1]
        opts.sort(key=lambda i: -gains[i])
        for i in opts:
            res = rec(covered | ball[cands[i]], chosen + [cands[i]])
            if res is not None:
                return res
            if nodes[0] > budget:
                return None
        return None

    return rec(0, [])


def _extend_cover(n, edges, d, D, deadline, rng, restarts, always_random=False):
    """Add vertices whose neighbourhoods cover everything within distance D-1."""
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
            if D >= 4 and time.monotonic() < deadline:
                chosen = _exact_cover(cands, ball, full, d, 2000)
            if not chosen:
                for attempt in range(restarts):
                    if time.monotonic() >= deadline:
                        break
                    chosen = _greedy_cover(cands, ball, full, d, rng,
                                           always_random or attempt > 0)
                    if chosen:
                        break
            if not chosen and time.monotonic() < deadline:
                chosen = _ls_cover(cands, ball, full, d, n, deadline, rng, 400)
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
    """Join deficient opposite-side vertices with leftover spare degree."""
    edges = list(edges)
    adj = _adj_list(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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


def _grow(n, edges, d, D, deadline, rng, restarts=200, always_random=False):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, restarts, always_random)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW: paired-vertex insertion (edge-coupled pair grow).
#
# Adds two new vertices X (side 0) and Y (side 1) joined by the edge X-Y.
# X is joined to a cover S of old side-1 vertices and Y to a cover T of old
# side-0 vertices, where each cover uses at most d-1 vertices and reaches all
# old vertices within distance D-1. Then every old vertex is within distance D
# of X and of Y, and old distances never increase. Two vertices are added per
# success, and it can use slack that single-vertex covers cannot, because the
# two covers draw from opposite sides and so never compete for the same slots.
# ----------------------------------------------------------------------------

def _pair_grow(n, edges, d, D, deadline, rng, tries=20):
    adj = _adj_list(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    ball = _balls_radius(n, adj, D - 1)
    full = (1 << n) - 1
    c0 = [s for s in range(n) if color[s] == 0 and deg[s] < d]
    c1 = [s for s in range(n) if color[s] == 1 and deg[s] < d]
    if not c0 or not c1:
        return None
    for _ in range(tries):
        if time.monotonic() >= deadline:
            break
        S = _greedy_cover(c1, ball, full, d - 1, rng, True)
        if not S:
            continue
        T = _greedy_cover(c0, ball, full, d - 1, rng, True)
        if not T:
            continue
        X, Y = n, n + 1
        E = list(edges) + [(X, Y)] + [(s, X) for s in S] + [(t, Y) for t in T]
        return n + 2, E
    return None


def _pair_loop(n, edges, d, D, deadline, rng):
    """Repeatedly apply paired insertion, then saturate spare degree."""
    cn, ce = n, list(edges)
    while time.monotonic() < deadline:
        r = _pair_grow(cn, ce, d, D, deadline, rng)
        if r is None:
            break
        cn, ce = r[0], _saturate_edges(r[0], r[1], d, rng)
    return cn, ce


# ----------------------------------------------------------------------------
# Arc / haar fallbacks.
# ----------------------------------------------------------------------------

# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    moore = lib.moore_bound(d, D)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if best_n < moore and pg is not None:
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.25 * time_limit, rng, 200)
            consider(n2, e2)
            for n_c, e_c in _arc_extensions(d, start + 0.35 * time_limit,
                                            random.Random(seed * 7919 + d)):
                consider(n_c, e_c)

    if D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        twin_deadline = start + 0.35 * time_limit
        for idx, q in enumerate(qs):
            now = time.monotonic()
            if now >= twin_deadline:
                break
            gq = _gq_w(q)
            consider(gq[0], gq[1])
            share = (twin_deadline - now) / (len(qs) - idx)
            tn, te = _twin_augment(gq[0], gq[1], d, rng, time.monotonic() + share)
            consider(tn, te)
            # New: paired insertion on the twin-augmented base.
            pn, pe = _pair_loop(tn, te, d, D, min(start + 0.45 * time_limit,
                                                  time.monotonic() + 0.08 * time_limit), rng)
            consider(pn, pe)
            n2, e2 = _grow(tn, te, d, D,
                           min(start + 0.5 * time_limit, time.monotonic() + 0.03 * time_limit),
                           rng, 300, False)
            consider(n2, e2)

    if best_n >= moore:
        return best

    # Main search loop.
    main_end = start + (0.80 if D >= 4 else 0.80) * time_limit
    while time.monotonic() < main_end and best_n < moore:
        r = rng.random()
        if D == 4 and r < 0.5:
            # Paired insertion on the current best.
            pn, pe = _pair_loop(best[0], best[1], d, D,
                                min(main_end, time.monotonic() + 0.05 * time_limit), rng)
            consider(pn, pe)
            # Re-randomise the saturation so the next pass explores differently.
            pn2, pe2 = _pair_loop(best[0], _saturate_edges(best[0], best[1], d, rng), d, D,
                                  min(main_end, time.monotonic() + 0.03 * time_limit), rng)
            consider(pn2, pe2)
            continue
        if D >= 3 and r < 0.8:
            short = min(main_end, time.monotonic() + 0.05 * time_limit)
            tn, te = _twin_augment(best[0], best[1], d, rng, short)
            consider(tn, te)
            n2, e2 = _grow(tn, te, d, D,
                           min(main_end, time.monotonic() + 0.02 * time_limit),
                           rng, 200, True)
            consider(n2, e2)
            continue
        short = min(main_end, time.monotonic() + 0.03 * time_limit)
        n2, e2 = _grow(best[0], best[1], d, D, short, rng, 200, True)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
