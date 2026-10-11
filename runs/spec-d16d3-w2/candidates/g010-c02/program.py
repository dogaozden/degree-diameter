"""Diameter-3 bipartite search: arc-extended projective planes, then greedy vertex
addition with an exact set-cover step.

Every addition keeps diameter <= 3 by construction. A new vertex x on side s is
joined to a set T of spare vertices on the other side. The cover test requires
every side-s vertex to share a neighbour with x, and every other-side vertex to lie
within distance 2 of T. Adding vertices and edges never increases an existing
distance, so the graph stays valid. Every returned graph is still checked with
lib.is_valid, and the best valid candidate is kept.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

_LP = None  # line_points for the current q, set in _arc_extensions


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


def _arc_graph(m, edges, point_lines, S):
    """Old PG incidence plus a new A-vertex (twin of point P) and a new B-vertex (twin of line j) per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in _LP[j]:
            E.append((Q, b))
    return n, E


def _saturate(n, edges, m, k, d, rng):
    """Add every missing X-Y edge while both endpoints have spare degree <= d."""
    E = set()
    for u, v in edges:
        E.add((u, v) if u < v else (v, u))
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    X = [v for v in range(n) if v < m or 2 * m <= v < 2 * m + k]
    Y = [v for v in range(n) if m <= v < 2 * m or v >= 2 * m + k]
    spare_x = [v for v in X if deg[v] < d]
    spare_y = [v for v in Y if deg[v] < d]
    pairs = [(x, y) for x in spare_x for y in spare_y]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d:
            continue
        key = (x, y) if x < y else (y, x)
        if key in E:
            continue
        E.add(key)
        deg[x] += 1
        deg[y] += 1
    return n, sorted(E)


def _arc_extensions(d, deadline, rng):
    """Return a list of ((n, raw_edges), (n, saturated_edges)) for each prime power q with q + 1 <= d."""
    global _LP
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        _LP = line_points
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, S)
        n_s, e_s = _saturate(n_c, e_c, m, len(S), d, rng)
        out.append(((n_c, e_c), (n_s, e_s)))
    return out


def _pg_base(d):
    """Projective plane incidence graph for the largest prime power q with q + 1 <= d, or None."""
    qs = [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)]
    if not qs:
        return None
    return lib.projective_plane_incidence(qs[0])


# ----------------------------------------------------------------------------
# Greedy vertex addition with exact set-cover search (diameter 3).
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Side labels (0/1) of a bipartite graph, by BFS from each unlabelled vertex."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    side = [-1] * n
    for s0 in range(n):
        if side[s0] != -1:
            continue
        side[s0] = 0
        stack = [s0]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if side[v] == -1:
                    side[v] = 1 - side[u]
                    stack.append(v)
    return side


def _masks(n, adj):
    """nb[v] = open neighbourhood bitmask; r2[v] = bitmask of all vertices within distance 2 of v."""
    nb = [0] * n
    for v in range(n):
        m = 0
        for u in adj[v]:
            m |= 1 << u
        nb[v] = m
    cl = [nb[v] | (1 << v) for v in range(n)]
    r2 = []
    for v in range(n):
        m = cl[v]
        for u in adj[v]:
            m |= cl[u]
        r2.append(m)
    return nb, r2


def _cover(adj, nb, r2, side_mask, s, d, rng, deadline):
    """Find T (spare vertices on side 1-s, |T| <= d) for a new vertex on side s, or None.

    Every side-s vertex must share a neighbour with the new vertex (T covers it),
    and every side-(1-s) vertex must be within distance 2 of T.
    """
    full = side_mask[s]
    other = side_mask[1 - s]
    budget = [400]
    out = [None]

    def dfs(T, covered):
        if budget[0] <= 0 or time.monotonic() > deadline:
            return False
        budget[0] -= 1
        unc = full & ~covered
        if unc == 0:
            R = 0
            for y in T:
                R |= r2[y]
            if (R & other) == other:
                out[0] = list(T)
                return True
            return False
        if len(T) >= d:
            return False
        # Branch on the uncovered side-s vertex with the fewest spare options.
        best = None
        x = unc
        cnt = 0
        while x and cnt < 40:
            low = x & -x
            x ^= low
            u = low.bit_length() - 1
            cnt += 1
            opts = [y for y in adj[u] if len(adj[y]) < d]
            if best is None or len(opts) < len(best):
                best = opts
                if len(opts) <= 1:
                    break
        if not best:
            return False
        rng.shuffle(best)
        best.sort(key=lambda y: -(nb[y] & unc).bit_count())
        for y in best[:6]:
            T.append(y)
            if dfs(T, covered | nb[y]):
                return True
            T.pop()
        return False

    dfs([], 0)
    return out[0]


def _grow(n, edges, d, deadline, rng):
    """Repeatedly add valid vertices until no cover exists (or the deadline passes)."""
    side = _two_color(n, edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    fails = 0
    while fails < 30 and time.monotonic() < deadline:
        nb, r2 = _masks(n, adj)
        side_mask = [0, 0]
        for v in range(n):
            side_mask[side[v]] |= 1 << v
        s = rng.randrange(2)
        T = _cover(adj, nb, r2, side_mask, s, d, rng, deadline)
        if T is None:
            s = 1 - s
            T = _cover(adj, nb, r2, side_mask, s, d, rng, deadline)
        if T is None:
            fails += 1
            continue
        fails = 0
        v = n
        n += 1
        side.append(s)
        adj.append(set(T))
        for y in T:
            adj[y].add(v)
    return n, adj, side


def _saturate_adj(n, adj, side, d, rng):
    """Add X-Y edges between spare vertices (only shortens distances, so validity is kept)."""
    xs = [v for v in range(n) if side[v] == 0 and len(adj[v]) < d]
    ys = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
    pairs = [(x, y) for x in xs for y in ys if y not in adj[x]]
    rng.shuffle(pairs)
    for x, y in pairs:
        if len(adj[x]) < d and len(adj[y]) < d and y not in adj[x]:
            adj[x].add(y)
            adj[y].add(x)


def _adj_to_edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


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
# Simulated annealing over bi-Cayley voltage lifts.
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
    """Permutation g -> mul(g, s) of the group."""
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
    """Simulated annealing over voltages and per-layer B-assignments."""
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pairs = _arc_extensions(d, start + 0.1 * time_limit, random.Random(seed * 7919 + d))
        starts = []
        for raw, sat in pairs:
            consider(sat[0], sat[1])
            starts.append(raw)
        starts.sort(key=lambda t: -t[0])
        starts = starts[:2]
        pg = _pg_base(d)
        if pg is not None:
            starts.append(pg)

        if D == 3 and starts:
            grow_end = start + 0.6 * time_limit
            for i, (n0, e0) in enumerate(starts):
                consider(n0, e0)
                now = time.monotonic()
                slot_end = now + max(0.0, grow_end - now) / (len(starts) - i)
                n1, adj, side = _grow(n0, e0, d, slot_end, random.Random(seed + 31 * i + 7))
                _saturate_adj(n1, adj, side, d, rng)
                consider(n1, _adj_to_edges(n1, adj))

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Annealed group voltage lifts for the remaining time.
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

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
