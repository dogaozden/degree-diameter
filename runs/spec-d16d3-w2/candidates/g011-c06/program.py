import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction A (D = 3): arc-extended projective plane incidence graphs.
#
# Start from the incidence graph of PG(2, q). With s = d - q - 1 spare degree,
# choose S (a set of points, also read as lines) with every line containing at
# most s points of S. Add a new X-vertex per P in S (joined to lines through P)
# and a new Y-vertex per j in S (joined to points on line j). Diameter stays 3.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, point_lines, line_points, index) for PG(2, q); points and lines share indices 0..m-1."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, point_lines, line_points, index


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
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _saturate(n, edges, m, k, d, rng):
    """Add missing X-Y edges while both endpoints have spare degree. Never increases distances."""
    E = set((min(u, v), max(u, v)) for u, v in edges)
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    X = [v for v in range(n) if v < m or 2 * m <= v < 2 * m + k]
    Y = [v for v in range(n) if m <= v < 2 * m or v >= 2 * m + k]
    sx = [v for v in X if deg[v] < d]
    sy = [v for v in Y if deg[v] < d]
    pairs = [(x, y) for x in sx for y in sy]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d:
            continue
        key = (min(x, y), max(x, y))
        if key in E:
            continue
        E.add(key)
        deg[x] += 1
        deg[y] += 1
    return n, sorted(E)


def _arc_base(d, q, rng, deadline):
    """Return (n, edges) of the arc-extended PG(2,q) graph for degree d, or None."""
    s = d - q - 1
    if s < 0:
        return None
    m, point_lines, line_points, index = _pg_data(q)
    cands = [_greedy_arc(m, s, point_lines, line_points, rng, 30, deadline)]
    if s >= 2:
        cs = _conic_set(q, index, lib.GF(q))
        if _loads_ok(cs, s, m, point_lines, line_points):
            cands.append(cs)
    S = max(cands, key=len)
    if not _loads_ok(S, s, m, point_lines, line_points):
        S = []
    k = len(S)
    n = 2 * m + 2 * k
    E = []
    for P in range(m):
        for L in point_lines[P]:
            E.append((P, m + L))
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return _saturate(n, E, m, k, d, rng)


# ----------------------------------------------------------------------------
# Construction B (D = 3, the new bold part): local search that grows a valid
# diameter-3 bipartite graph by adding one X-vertex and one Y-vertex at a time.
#
# State: bipartite edge set with degrees <= d. Cost = number of unordered pairs
# at distance > 3 (computed with bitmask BFS). Moves: remove a random edge and
# add a random edge between spare vertices, or add an edge between spare
# vertices. Annealed acceptance. Whenever cost hits 0 the graph is valid and
# gets recorded, then two fresh vertices are added.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs count)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _two_color(n, edges):
    """Proper 2-colouring of a connected bipartite graph, or None."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    st.append(v)
                elif col[v] == col[u]:
                    return None
    return col


def _repair(n0, E0, d, D, side0, cap, deadline, rng):
    """Anneal and grow from a valid base graph. Returns the largest valid (n, edges) found."""
    n = n0
    side = list(side0)
    adj = [set() for _ in range(n)]
    for u, v in E0:
        adj[u].add(v)
        adj[v].add(u)
    best = (n0, list(E0))
    cost = _bad(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while time.monotonic() < deadline:
        if cost == 0:
            if n > best[0]:
                best = (n, [(u, v) for u in range(n) for v in adj[u] if u < v])
            if n + 2 > cap:
                break
            adj.append(set())
            adj.append(set())
            side.append(0)
            side.append(1)
            n += 2
            cost = _bad(n, adj, D)
            continue

        frac = min(1.0, (time.monotonic() - t0) / span)
        T = 0.5 * (0.02 / 0.5) ** frac
        Xs = [v for v in range(n) if side[v] == 0]

        removed = None
        if rng.random() < 0.5:
            u = rng.choice(Xs)
            if adj[u]:
                v = rng.choice(list(adj[u]))
                adj[u].discard(v)
                adj[v].discard(u)
                removed = (u, v)

        spX = [v for v in Xs if len(adj[v]) < d]
        spY = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
        added = None
        if spX and spY:
            for _ in range(40):
                x = rng.choice(spX)
                y = rng.choice(spY)
                if y not in adj[x]:
                    added = (x, y)
                    break
        if added is None:
            if removed is not None:
                u, v = removed
                adj[u].add(v)
                adj[v].add(u)
            continue

        x, y = added
        adj[x].add(y)
        adj[y].add(x)
        new_cost = _bad(n, adj, D)
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new_cost
        else:
            adj[x].discard(y)
            adj[y].discard(x)
            if removed is not None:
                u, v = removed
                adj[u].add(v)
                adj[v].add(u)

    if cost == 0 and n > best[0]:
        best = (n, [(u, v) for u in range(n) for v in adj[u] if u < v])
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

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
# Voltage-lift annealing over semidirect groups (used for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
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
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
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

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.3, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Construction A: arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = []
        for q in range(2, min(d - 1, 23) + 1):
            if not lib.is_prime_power(q):
                continue
            res = _arc_base(d, q, rng, deadline)
            if res is not None:
                cands.append(res)
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands[:2]:
            consider(n_c, e_c)

    # Construction B (D = 3): grow the best base by annealed local search.
    if D == 3 and best[0] < lib.moore_bound(d, D):
        side = _two_color(best[0], best[1])
        if side is not None:
            res = _repair(best[0], best[1], d, D, side, lib.moore_bound(d, D),
                          deadline, random.Random(seed * 31 + 7))
            consider(res[0], res[1])

    # D >= 4: generalized quadrangle and voltage lifts.
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D >= 4:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
