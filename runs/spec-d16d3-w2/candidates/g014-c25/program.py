import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. Choose a set S of points such that every line holds <= s points
# of S and every point lies on <= s lines indexed by S. For each P in S add a
# new X-vertex joined to the q+1 lines through P; for each j in S add a new
# Y-vertex joined to the q+1 points on line j.
#
# Augmentation (new this round): a new vertex v on side s may be attached to any
# set T of opposite-side vertices with spare degree, provided the union of the
# neighbourhoods of T covers every existing vertex on side s. Then:
#   - every existing same-side vertex is at distance 2 from v;
#   - every opposite-side vertex y has a neighbour z on side s, and z has a
#     neighbour in T, so y is at distance <= 3 from v;
#   - adding edges never lengthens a path, so the old diameter bound holds.
# Each accepted vertex adds one to the order. Greedy set cover picks T, with
# random tie-breaking so repeated attempts explore different covers.
#
# Saturation (remaining spare X-Y edges) is applied last. It adds no vertices,
# so it only runs on capacity that augmentation could not use.
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


def _arc_base(q, d, rng, deadline):
    """Pre-augmentation extended graph for prime power q: (n, edges, side) or None."""
    s = d - q - 1
    if s < 1:
        return None
    m, edges, point_lines, line_points, index, pts = _pg_data(q)
    cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)]
    if s >= 2:
        cs = _conic_set(q, index, lib.GF(q))
        if _loads_ok(cs, s, m, point_lines, line_points):
            cands.append(cs)
    S = max(cands, key=len)
    if not S or not _loads_ok(S, s, m, point_lines, line_points):
        return None
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
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _augment(n, E, side, d, deadline, rng, max_fail=60):
    """Greedily add vertices, each covering every existing vertex on its own side via spare opposite-side vertices.

    side[v] is 0 or 1. A new vertex of side w is joined to a set T of side (1-w) vertices
    with spare degree whose neighbourhoods cover all existing side-w vertices.
    Returns (n, edges, side).
    """
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    side = list(side)
    fails = 0
    while fails < max_fail and time.monotonic() < deadline:
        want = rng.randrange(2)
        uncovered = {v for v in range(n) if side[v] == want}
        cand = [y for y in range(n) if side[y] != want and len(adj[y]) < d]
        T = []
        chosen = set()
        while uncovered and len(T) < d:
            best, best_key = None, -1.0
            for y in cand:
                if y in chosen:
                    continue
                c = 0
                for z in adj[y]:
                    if z in uncovered:
                        c += 1
                if c == 0:
                    continue
                key = c + 0.9 * rng.random()
                if key > best_key:
                    best, best_key = y, key
            if best is None:
                break
            T.append(best)
            chosen.add(best)
            uncovered -= adj[best]
        if uncovered or not T:
            fails += 1
            continue
        fails = 0
        new = n
        n += 1
        side.append(want)
        adj.append(set(T))
        for y in T:
            adj[y].add(new)
    E2 = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, E2, side


def _saturate(n, E, side, d, rng):
    """Add missing cross-side edges while both endpoints have spare degree (only shortens distances)."""
    adj = [set() for _ in range(n)]
    for u, v in E:
        adj[u].add(v)
        adj[v].add(u)
    deg = [len(a) for a in adj]
    X = [v for v in range(n) if side[v] == 0 and deg[v] < d]
    Y = [v for v in range(n) if side[v] == 1 and deg[v] < d]
    pairs = [(x, y) for x in X for y in Y]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d or y in adj[x]:
            continue
        adj[x].add(y)
        adj[y].add(x)
        deg[x] += 1
        deg[y] += 1
    return n, [(u, v) for u in range(n) for v in adj[u] if u < v]


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
# Simulated annealing over bi-Cayley voltage lifts (unchanged from parent).
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
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

    # Arc-extended projective plane graphs, augmented with extra vertices, then saturated.
    # Diameter 3, so valid for all D >= 3.
    if D >= 3:
        aug_rng = random.Random(seed * 104729 + d)
        bases = []
        for q in range(2, min(d - 1, 23) + 1):
            if time.monotonic() > deadline:
                break
            if not lib.is_prime_power(q):
                continue
            b = _arc_base(q, d, random.Random(seed * 7919 + q), deadline)
            if b is not None:
                bases.append(b)
        bases.sort(key=lambda t: -t[0])
        top = bases[:3]
        for idx, (nb, Eb, sideb) in enumerate(top):
            now = time.monotonic()
            share = max(0.0, deadline - now) / (len(top) - idx)
            n2, E2, side2 = _augment(nb, Eb, sideb, d, now + share, aug_rng)
            n2, E2 = _saturate(n2, E2, side2, d, aug_rng)
            consider(n2, E2)
        for nb, Eb, sideb in bases:
            if nb > best_n:
                n2, E2 = _saturate(nb, Eb, sideb, d, aug_rng)
                consider(n2, E2)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: annealed group voltage lifts. For D >= 5 use larger bases.
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
