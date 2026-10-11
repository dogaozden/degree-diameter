import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, leaving spare capacity s = d - q - 1. Choose a point set S with
# every line holding <= s points of S and every point on <= s lines indexed by S.
# For each P in S add an A-vertex on the lines through P; for each j in S add a
# B-vertex on the points of line j. Order 2(q^2+q+1) + 2|S|.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, pl, lp, index


def _loads_ok(S, s, m, pl, lp):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, trials, deadline):
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
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
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


def _arc_graph(m, edges, S, pl, lp):
    """Return (n, edges, side) for the arc-extended incidence graph."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in pl[P]:
            E.append((a, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _arc_extensions(d, deadline, rng):
    """Candidates (n, edges, m, pl, lp, side) for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        n_c, E_c, side = _arc_graph(m, edges, S, pl, lp)
        out.append((n_c, E_c, m, pl, lp, side))
    return out


# ----------------------------------------------------------------------------
# Bipartite repair annealing (D = 3): add two vertices (one per side) and
# anneal over bipartite edge sets until no pair is at distance > D.
# ----------------------------------------------------------------------------

def _to_adj(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


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


# ----------------------------------------------------------------------------
# Validity-checked local search (D = 3): add stars (lines through a point or
# points on a line) or remove vertices; keep only moves that pass lib.is_valid.
# ----------------------------------------------------------------------------

def _local_search(E0, m, pl, lp, d, D, deadline, rng):
    adj = {}

    def link(u, v):
        adj.setdefault(u, set()).add(v)
        adj.setdefault(v, set()).add(u)

    def unlink_vertex(v):
        nb = adj.pop(v, set())
        for u in nb:
            s = adj[u]
            s.discard(v)
            if not s:
                del adj[u]
        return nb

    def raw():
        return [(u, v) for u in adj for v in adj[u] if u < v]

    def valid():
        n, E = lib.relabel(raw())
        return lib.is_valid(n, E, d, D)

    def load(E):
        adj.clear()
        for u, v in E:
            link(u, v)

    n0 = max(max(e) for e in E0) + 1
    best_E = list(E0)
    load(E0)
    cur = len(adj)
    best_cnt = cur
    nxt = n0
    T = 0.7
    stale = 0

    while time.monotonic() < deadline:
        stale += 1
        if stale > 4000:
            load(best_E)
            cur = len(adj)
            nxt = max(max(e) for e in best_E) + 1
            stale = 0
            continue

        if rng.random() < 0.4:
            if rng.random() < 0.5:
                cand = [m + L for L in pl[rng.randrange(m)]]
            else:
                cand = list(lp[rng.randrange(m)])
            nb = [u for u in cand if len(adj.get(u, ())) < d]
            if len(nb) < 2:
                continue
            x = nxt
            nxt += 1
            for u in nb:
                link(x, u)
            kind, vid, saved = 'add', x, nb
        else:
            if not adj:
                continue
            v = rng.choice(list(adj))
            nb = unlink_vertex(v)
            kind, vid, saved = 'rem', v, nb

        def undo():
            if kind == 'add':
                unlink_vertex(vid)
            else:
                adj[vid] = set()
                for u in saved:
                    link(vid, u)

        delta = len(adj) - cur
        if delta < 0 and rng.random() >= math.exp(delta / T):
            undo()
            continue
        if not valid():
            undo()
            continue
        cur = len(adj)
        if cur > best_cnt:
            best_cnt = cur
            best_E = raw()
            stale = 0

    n, E = lib.relabel(best_E)
    if lib.is_valid(n, E, d, D):
        return n, E
    return None


# ----------------------------------------------------------------------------
# Annealed group voltage lifts (used for D != 3 and leftover time).
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
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (D = 4).
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, E

    if D >= 3:
        cands = _arc_extensions(d, start + 0.2 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for c in cands:
            consider(c[0], c[1])

        if D == 3 and cands:
            n_a, E_a, m, pl, lp, side_a = cands[0]

            # Phase A: repair annealing, adding two vertices at a time.
            adj = _to_adj(n_a, E_a)
            side = list(side_a)
            n = n_a
            repair_deadline = start + 0.45 * time_limit
            while time.monotonic() < repair_deadline:
                n_t = n + 2
                if n_t > lib.moore_bound(d, D):
                    break
                adj.append(set())
                adj.append(set())
                side = side + [0, 1]
                if not _repair(n_t, adj, side, d, D, rng, repair_deadline):
                    break
                E2 = [(x, y) for x in range(n_t) for y in adj[x] if x < y]
                if not lib.is_valid(n_t, E2, d, D):
                    break
                consider(n_t, E2)
                n = n_t

            # Phase B: validity-checked local search from the best PG-derived graph.
            start_E = best_E if best_n >= n_a else E_a
            res = _local_search(start_E, m, pl, lp, d, D, deadline,
                                random.Random(seed * 31 + 7))
            if res is not None:
                consider(res[0], res[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed voltage lifts for remaining time (main search for D != 3).
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
