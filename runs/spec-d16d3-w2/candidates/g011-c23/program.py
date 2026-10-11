import itertools
import math
import random
import time

import lib

_MAX_Q = 31


# ----------------------------------------------------------------------------
# Generic graph helpers.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _colors(n, adj):
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
# Projective plane data and arc-extended incidence graphs (diameter 3).
#
# Old incidence graph of PG(2,q): points 0..m-1, lines m..2m-1, degree q+1.
# With spare s = d-q-1, choose a point set S with every line containing <= s
# points of S and every point on <= s lines indexed by S. Add an A-vertex per
# point of S (joined to its q+1 lines) and a B-vertex per line of S (joined to
# its q+1 points). Diameter stays 3.
# ----------------------------------------------------------------------------

def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


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
    conic = _conic_set(q, index, lib.GF(q))
    return m, edges, point_lines, line_points, conic


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _random_arc(m, s, point_lines, line_points, rng):
    order = list(range(m))
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
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):  # S is also a set of line indices (same vectors)
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


# ----------------------------------------------------------------------------
# Growth operations (all preserve bipartiteness and diameter <= D for D >= 3).
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


def _grow_cover(n, edges, d, D, deadline, rng):
    """Add new vertices whose neighbourhoods cover everything within distance D-1."""
    if D < 2:
        return n, list(edges)
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _colors(n, adj)
    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(8):
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


def _grow_twins(n, edges, d, D, rng, deadline):
    """Add twins (same neighbourhood) of vertices whose neighbours have spare degree."""
    if D < 2:
        return n, list(edges)
    edges = list(edges)
    adj = _adjacency(n, edges)
    while time.monotonic() < deadline:
        elig = [v for v in range(n)
                if adj[v] and all(len(adj[u]) < d for u in adj[v])]
        if not elig:
            break
        v = rng.choice(elig)
        t = n
        n += 1
        adj.append(list(adj[v]))
        for u in adj[v]:
            adj[u].append(t)
            edges.append((u, t))
    return n, edges


def _saturate(n, edges, d, rng):
    """Add missing X-Y edges while both endpoints have spare degree (never lengthens distances)."""
    E = set()
    for u, v in edges:
        E.add((u, v) if u < v else (v, u))
    adj = _adjacency(n, list(E))
    deg = [len(a) for a in adj]
    color = _colors(n, adj)
    X = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    Y = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(x, y) for x in X for y in Y
             if ((x, y) if x < y else (y, x)) not in E]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] < d and deg[y] < d:
            E.add((x, y) if x < y else (y, x))
            deg[x] += 1
            deg[y] += 1
    return sorted(E)


def _trial(dat, s, d, D, rng, deadline):
    m, edges, point_lines, line_points, conic = dat
    S = None
    if rng.random() < 0.25 and _loads_ok(conic, s, m, point_lines, line_points):
        S = list(conic)
    else:
        S = _random_arc(m, s, point_lines, line_points, rng)
        if S and rng.random() < 0.5:
            S = S[:rng.randrange(len(S) + 1)]
    n, E = _arc_graph(m, edges, point_lines, line_points, S)
    if rng.random() < 0.7:
        n, E = _grow_cover(n, E, d, D, deadline, rng)
        n, E = _grow_twins(n, E, d, D, rng, deadline)
    else:
        n, E = _grow_twins(n, E, d, D, rng, deadline)
        n, E = _grow_cover(n, E, d, D, deadline, rng)
    E = _saturate(n, E, d, rng)
    return n, E


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    for q in range(min(d - 1, 8), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products, annealed (for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges_of(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges_of(k, G, darts, perms)
    return None


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
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, list(e))
            best_n = n

    total_deadline = start + 0.75 * time_limit

    if D >= 3:
        arc_deadline = start + (0.70 if D == 3 else 0.30) * time_limit
        qs = [q for q in range(2, min(d - 1, _MAX_Q) + 1) if lib.is_prime_power(q)]
        if qs:
            # Plain PG(2,q) with the largest q such that q+1 <= d.
            qmax = max(qs)
            n0, e0 = lib.projective_plane_incidence(qmax)
            consider(n0, e0)

            pool = [q for q in qs if d - q - 1 >= 1]
            if pool:
                cache = {}
                weights = [2 * (q * q + q + 1) for q in pool]
                while time.monotonic() < arc_deadline:
                    q = rng.choices(pool, weights)[0]
                    if q not in cache:
                        cache[q] = _pg_data(q)
                    s = d - q - 1
                    trial_dl = min(arc_deadline, time.monotonic() + 3.0)
                    n_c, e_c = _trial(cache[q], s, d, D, rng, trial_dl)
                    consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < total_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, total_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
