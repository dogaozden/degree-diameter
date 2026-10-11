import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Caches for finite-field data and projective planes.
# ----------------------------------------------------------------------------

_PG = {}
_GF = {}


def _gf(q):
    if q not in _GF:
        _GF[q] = lib.GF(q)
    return _GF[q]


def _pg(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q), cached.

    Points are indices 0..m-1, lines are indices 0..m-1 (the same vectors).
    """
    if q not in _PG:
        n2, edges = lib.projective_plane_incidence(q)
        m = n2 // 2
        pts = lib.projective_points(q)
        point_lines = [[] for _ in range(m)]
        line_points = [[] for _ in range(m)]
        for u, v in edges:
            point_lines[u].append(v - m)
            line_points[v - m].append(u)
        index = {p: i for i, p in enumerate(pts)}
        _PG[q] = (m, edges, point_lines, line_points, index)
    return _PG[q]


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3), as in the parent.
# Old points are side 0, old lines side 1; new A-vertices (side 0) join the
# lines through each P in S, new B-vertices (side 1) join the points on each
# line j in S. Degree loads are capped by s = d - q - 1.
# ----------------------------------------------------------------------------

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
    """Return (n, adj, side) for the arc-extended graph with adjacency sets."""
    k = len(S)
    n = 2 * m + 2 * k
    adj = [set() for _ in range(n)]
    side = [0] * m + [1] * m + [0] * k + [1] * k
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            adj[x].add(m + L)
            adj[m + L].add(x)
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            adj[b].add(Q)
            adj[Q].add(b)
    return n, adj, side


# ----------------------------------------------------------------------------
# NEW: cover-based augmentation.
#
# Adding a vertex x on side t, joined to a set Z of spare vertices on the
# opposite side, keeps the graph valid for diameter 3 exactly when every
# existing vertex lies within distance 2 of some z in Z (distances between old
# vertices can only shrink). So we look for a set Z of at most d spare
# vertices whose distance-2 balls cover everything, found by randomized greedy
# set cover on bitmasks. Each success adds one vertex and uses spare degree.
# ----------------------------------------------------------------------------

def _balls2(n, adj):
    cl = []
    for v in range(n):
        r = 1 << v
        for u in adj[v]:
            r |= 1 << u
        cl.append(r)
    ball2 = []
    for v in range(n):
        r = cl[v]
        for u in adj[v]:
            r |= cl[u]
        ball2.append(r)
    return ball2


def _cover(C, ball2, U, d, rng, tries):
    """Find Z subset of C, |Z| <= d, with union of ball2 equal to U; None if not found."""
    for attempt in range(tries):
        avail = C[:]
        if attempt > 0:
            rng.shuffle(avail)
        cur = 0
        Z = []
        while cur != U and len(Z) < d:
            bg = 0
            bc = -1
            for c in avail:
                g = (ball2[c] & ~cur).bit_count()
                if g > bg:
                    bg = g
                    bc = c
            if bc < 0:
                break
            Z.append(bc)
            cur |= ball2[bc]
            avail = [c for c in avail if c != bc]
        if cur == U:
            return Z
    return None


def _augment(n, adj, side, d, rng, deadline, tries):
    """Greedily add vertices whose neighbourhoods cover everything within distance 2."""
    while time.monotonic() < deadline:
        ball2 = _balls2(n, adj)
        U = (1 << n) - 1
        sides = [0, 1]
        rng.shuffle(sides)
        grew = False
        for t in sides:
            C = [v for v in range(n) if side[v] == 1 - t and len(adj[v]) < d]
            if not C:
                continue
            Z = _cover(C, ball2, U, d, rng, tries)
            if Z is not None:
                x = n
                n += 1
                adj.append(set(Z))
                side.append(t)
                for z in Z:
                    adj[z].add(x)
                grew = True
                break
        if not grew:
            break
    return n


def _to_edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _arc_search(d, deadline, rng, consider):
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]
    if not qs:
        return
    while time.monotonic() < deadline:
        q = qs[-1] if rng.random() < 0.5 else rng.choice(qs)
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg(q)
        S = []
        if s >= 1:
            if s >= 2 and rng.random() < 0.4:
                cs = _conic_set(q, index, _gf(q))
                if _loads_ok(cs, s, m, point_lines, line_points):
                    S = cs
            if not S:
                S = _greedy_arc(m, s, point_lines, line_points, rng, 4, deadline)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n, adj, side = _arc_graph(m, edges, point_lines, line_points, S)
        n = _augment(n, adj, side, d, rng, deadline, 10)
        consider(n, _to_edges(n, adj))


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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (for D >= 4).
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
# Entry point.
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
    st = {"n": 2 * d, "g": lib.haar_graph(d, range(d))}

    def consider(n, e):
        if n > st["n"] and lib.is_valid(n, e, d, D):
            st["n"] = n
            st["g"] = (n, e)

    if D >= 3:
        arc_deadline = deadline if D == 3 else start + 0.45 * time_limit
        _arc_search(d, arc_deadline, rng, consider)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D >= 4:
        ks = [1, 2, 2, 3, 4]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = st["n"] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    n, e = st["g"]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
