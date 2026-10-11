import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Graph utilities (set-based adjacency, bitmask balls).
# ----------------------------------------------------------------------------

def _adj_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _edge_list(n, adj):
    return [(x, y) for x in range(n) for y in adj[x] if x < y]


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


def _balls(n, adj, r):
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


def _bad_pairs(n, adj, D):
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# Projective plane incidence with independent point-arc (A) and line-arc (B)
# extensions. For D = 3 this is the main family.
#
# A-vertex per point P in SA, joined to the q+1 lines through P. Each line then
# gains at most s extra edges, so SA is a point set with every line holding <= s
# of its points. B-vertex per line j in SB, joined to the q+1 points on j. Each
# point gains at most s extra edges, so SB is a line set with every point on
# <= s of its lines. SA and SB are chosen independently; diameter stays 3.
# ----------------------------------------------------------------------------

def _pg(q):
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _best_pg(d):
    """Plain incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _conic(q, index):
    """Conic (plus nucleus for even q): a candidate arc, as an index set."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _capped_set(m, s, inc, rng, init, deadline):
    """Local search for a large set S of indices x such that every target t is hit by <= s chosen x.

    inc[x] lists the targets of candidate x. Moves: insert a free candidate; swap out a
    single blocker (plateau move); occasionally swap out two blockers.
    """
    cnt = [0] * m
    inS = [False] * m
    S = []

    def add(x):
        inS[x] = True
        S.append(x)
        for t in inc[x]:
            cnt[t] += 1

    def remove(x):
        inS[x] = False
        S.remove(x)
        for t in inc[x]:
            cnt[t] -= 1

    if init:
        tmp = [0] * m
        for x in init:
            for t in inc[x]:
                tmp[t] += 1
        if max(tmp) <= s:
            for x in init:
                add(x)

    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        sat = {t for t in inc[x] if cnt[t] >= s}
        if not sat:
            add(x)
        else:
            B = [y for y in S if any(t in sat for t in inc[y])]
            if len(B) == 1 or (len(B) == 2 and rng.random() < 0.05):
                for y in B:
                    remove(y)
                if all(cnt[t] < s for t in inc[x]):
                    add(x)
                else:
                    for y in B:
                        add(y)
                    continue
            else:
                continue
        if len(S) > len(best):
            best = list(S)
    return best


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    n = 2 * m + len(SA) + len(SB)
    E = list(edges)
    base_a = 2 * m
    for t, P in enumerate(SA):
        a = base_a + t
        for L in point_lines[P]:
            E.append((a, m + L))
    base_b = base_a + len(SA)
    for t, j in enumerate(SB):
        b = base_b + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_phase(d, D, rng, deadline, floor_n):
    """Search arc-extended PG(2, q) graphs for prime powers q with s = d - q - 1 >= 1."""
    cands = []
    for q in range(2, d - 1):
        s = d - q - 1
        if s < 1 or not lib.is_prime_power(q):
            continue
        m = q * q + q + 1
        ub = 2 * m + 2 * (s * m // (q + 1))
        if ub > floor_n:
            cands.append((ub, q, s))
    cands.sort(reverse=True)

    best, best_n = None, floor_n
    for idx, (ub, q, s) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        if ub <= best_n:
            continue
        share = (deadline - now) / (len(cands) - idx)
        m, edges, pl, lp, index = _pg(q)
        conic = _conic(q, index) if s >= 2 else None
        SA = _capped_set(m, s, pl, rng, conic, now + 0.5 * share)
        SB = _capped_set(m, s, lp, rng, conic, now + share)
        n, E = _arc_graph(m, edges, pl, lp, SA, SB)
        if n > best_n and lib.is_valid(n, E, d, D):
            best, best_n = (n, E), n
    return best


# ----------------------------------------------------------------------------
# Cover-based growth: add a vertex whose neighbourhood covers all vertices within
# D-1, then saturate spare degree. Both steps keep diameter <= D.
# ----------------------------------------------------------------------------

def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[x] & ~covered).bit_count() for x in pool]
        best_g = max(gains)
        if best_g == 0:
            break
        thr = max(1, best_g - 1) if (randomize and rng.random() < 0.5) else best_g
        opts = [i for i, g in enumerate(gains) if g >= thr]
        i = rng.choice(opts) if randomize else opts[0]
        x = pool.pop(i)
        chosen.append(x)
        covered |= ball[x]
    return chosen if covered == full else None


def _cover_grow(n, adj, d, D, deadline, rng):
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        color = _bipartition(n, adj)
        added = False
        for c in (0, 1):
            cands = [x for x in range(n) if color[x] == c and len(adj[x]) < d]
            if not cands:
                continue
            chosen = _greedy_cover(cands, ball, full, d, rng, False)
            att = 0
            while chosen is None and att < 30 and time.monotonic() < deadline:
                chosen = _greedy_cover(cands, ball, full, d, rng, True)
                att += 1
            if chosen:
                v = n
                n += 1
                adj.append(set())
                for x in chosen:
                    adj[x].add(v)
                    adj[v].add(x)
                added = True
                break
        if not added:
            break
    return n


def _saturate(n, adj, d, rng):
    color = _bipartition(n, adj)
    left = [x for x in range(n) if color[x] == 0 and len(adj[x]) < d]
    right = [x for x in range(n) if color[x] == 1 and len(adj[x]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d:
            adj[a].add(b)
            adj[b].add(a)


# ----------------------------------------------------------------------------
# Degree-preserving annealing repair: start from a graph with two fresh vertices
# (one per side) and anneal until no pair is at distance > D.
# ----------------------------------------------------------------------------

def _apply(adj, ops):
    for op, x, y in ops:
        if op == 'a':
            adj[x].add(y)
            adj[y].add(x)
        else:
            adj[x].discard(y)
            adj[y].discard(x)


def _propose(adj, side0, side1, d, rng):
    r = rng.random()
    if r < 0.6:
        x1 = rng.choice(side0)
        x2 = rng.choice(side0)
        if x1 == x2 or not adj[x1] or not adj[x2]:
            return None
        y1 = rng.choice(list(adj[x1]))
        y2 = rng.choice(list(adj[x2]))
        if y1 == y2 or y2 in adj[x1] or y1 in adj[x2]:
            return None
        return [('d', x1, y1), ('d', x2, y2), ('a', x1, y2), ('a', x2, y1)]
    if r < 0.8:
        x = rng.choice(side0)
        y = rng.choice(side1)
        if y in adj[x] or len(adj[x]) >= d or len(adj[y]) >= d:
            return None
        return [('a', x, y)]
    x1 = rng.choice(side0)
    if not adj[x1]:
        return None
    y1 = rng.choice(list(adj[x1]))
    if rng.random() < 0.5:
        y2 = rng.choice(side1)
        if y2 == y1 or y2 in adj[x1] or len(adj[y2]) >= d:
            return None
        return [('d', x1, y1), ('a', x1, y2)]
    x2 = rng.choice(side0)
    if x2 == x1 or y1 in adj[x2] or len(adj[x2]) >= d:
        return None
    return [('d', x1, y1), ('a', x2, y1)]


def _repair(n, adj, side, d, D, rng, deadline):
    side0 = [v for v in range(n) if side[v] == 0]
    side1 = [v for v in range(n) if side[v] == 1]
    cost = _bad_pairs(n, adj, D)
    T = 1.5
    while cost > 0:
        if time.monotonic() > deadline:
            return False
        T = max(0.1, T * 0.999)
        ops = _propose(adj, side0, side1, d, rng)
        if ops is None:
            continue
        _apply(adj, ops)
        c2 = _bad_pairs(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            undo = [('d' if op == 'a' else 'a', x, y) for op, x, y in reversed(ops)]
            _apply(adj, undo)
    return True


def _grow_repair(n, E, d, D, rng, grow_end, deadline, consider):
    adj = _adj_sets(n, E)
    n = _cover_grow(n, adj, d, D, grow_end, rng)
    _saturate(n, adj, d, rng)
    consider(n, _edge_list(n, adj))
    side = _bipartition(n, adj)
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline and n + 2 <= moore:
        adj2 = [set(a) for a in adj] + [set(), set()]
        side2 = side + [0, 1]
        if not _repair(n + 2, adj2, side2, d, D, rng, deadline):
            break
        E2 = _edge_list(n + 2, adj2)
        if not lib.is_valid(n + 2, E2, d, D):
            break
        n += 2
        adj, side = adj2, side2
        consider(n, E2)


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (D >= 4).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Annealed voltage lifts over semidirect products (D >= 4).
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


def _cost(k, G, D, darts, perms, limit=float("inf")):
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
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

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
        u = 1.0 - rng.random()
        limit = cost - T * math.log(u)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: diameter 2, and optimal for D = 2 (bipartite Moore bound 2d).
    best_n, best_E = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, list(best_E)

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    base = _best_pg(d)
    if base is not None:
        consider(base[0], base[1])

    if D == 3:
        arc = _arc_phase(d, D, rng, start + 0.55 * (deadline - start), best_n)
        if arc is not None:
            consider(arc[0], arc[1])
        _grow_repair(best_n, list(best_E), d, D, rng,
                     start + 0.7 * (deadline - start), deadline, consider)
    else:
        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            b = best_n // (2 * k)
            G = max(2, b + 1 + rng.randrange(0, max(3, b // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=1200)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
