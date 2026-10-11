import itertools
import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (valid for D >= 3).
#
# Start from the point-line incidence graph of PG(2, q). Each vertex has
# degree q+1, so with d >= q+1 it has spare capacity s = d - q - 1. Pick a set
# S of points with every line holding <= s points of S and every point on
# <= s lines indexed by S. For each P in S add an A-vertex joined to the q+1
# lines through P; for each j in S add a B-vertex joined to the q+1 points on
# line j. Then saturate: add every missing X-Y edge while both ends have spare
# degree. Adding edges never increases distances, so diameter 3 is preserved.
# Order is 2(q^2+q+1) + 2|S|. For d=16 (q=13, S = conic of size 14) this gives 394.
# ----------------------------------------------------------------------------

def _pg(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
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


def _saturate(n, edges, side, d, rng):
    """Add every missing X-Y edge while both endpoints have spare degree < d."""
    E = set((min(u, v), max(u, v)) for u, v in edges)
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    X = [v for v in range(n) if side[v] == 0 and deg[v] < d]
    Y = [v for v in range(n) if side[v] == 1 and deg[v] < d]
    pairs = [(x, y) for x in X for y in Y]
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
    return sorted(E)


def _arc_candidate(q, d, deadline, rng):
    """Return (n, edges, side) for the arc-extended PG(2,q) graph, or None."""
    s = d - q - 1
    if s < 0:
        return None
    m, edges, point_lines, line_points, index = _pg(q)
    cands = [[]]
    if s >= 1:
        cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
    if s >= 2:
        cs = _conic_set(q, index, lib.GF(q))
        if _loads_ok(cs, s, m, point_lines, line_points):
            cands.append(cs)
    S = max(cands, key=len)
    if not _loads_ok(S, s, m, point_lines, line_points):
        return None
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        for L in point_lines[P]:
            E.append((2 * m + t, m + L))
    for t, j in enumerate(S):
        for Q in line_points[j]:
            E.append((Q, 2 * m + k + t))
    side = [0 if (v < m or 2 * m <= v < 2 * m + k) else 1 for v in range(n)]
    E = _saturate(n, E, side, d, rng)
    return n, E, side


def _grow(n, E, side, d, D, rng, deadline):
    """Try to attach extra vertices to spare-degree vertices; keep only results that validate."""
    E = list(E)
    side = list(side)
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    fails = 0
    while time.monotonic() < deadline and fails < 200:
        w_side = rng.randrange(2)
        pool = [v for v in range(n) if deg[v] < d and side[v] != w_side]
        if not pool:
            fails += 1
            continue
        rng.shuffle(pool)
        k = rng.randint(max(1, d // 2), min(d, len(pool)))
        nb = pool[:k]
        newE = E + [(v, n) for v in nb]
        if lib.is_valid(n + 1, newE, d, D):
            E = newE
            deg.append(k)
            side.append(w_side)
            for v in nb:
                deg[v] += 1
            n += 1
            fails = 0
        else:
            fails += 1
    return n, E


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) baseline (D = 4).
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
    """W(q) for the largest prime power q <= min(d-1, 9), or None."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (D >= 4).
# ----------------------------------------------------------------------------

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


def _haar_try(d, rng):
    """Random Haar graph of Z_m with connection set of size d (degree d, bipartite)."""
    m = rng.randrange(d + 1, d + 40)
    S = [0] + rng.sample(range(1, m), d - 1)
    return lib.haar_graph(m, S)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Always-valid fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(cand):
        nonlocal best, best_n
        if cand is None:
            return
        n, e = cand
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Arc-extended projective plane graphs (valid for any D >= 3).
    if D >= 3:
        arc_rng = random.Random(seed * 7919 + d)
        best_arc = None
        qs = [q for q in range(2, d) if lib.is_prime_power(q) and (q <= 23 or q == d - 1)]
        for q in qs:
            if time.monotonic() > deadline:
                break
            cand = _arc_candidate(q, d, deadline, arc_rng)
            if cand is not None and (best_arc is None or cand[0] > best_arc[0]):
                best_arc = cand
        if best_arc is not None:
            n_a, E_a, side_a = best_arc
            consider((n_a, E_a))
            grow_deadline = deadline if D == 3 else start + 0.3 * time_limit
            n_g, E_g = _grow(n_a, E_a, side_a, d, D, arc_rng, grow_deadline)
            consider((n_g, E_g))

    # Generalized quadrangle (valid for D >= 4).
    if D >= 4 and time.monotonic() < deadline:
        consider(_best_gq(d))

    if D < 4:
        return best

    # Search for D >= 4: annealed group lifts, plus random Haar graphs for D >= 5.
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        if D >= 5 and rng.random() < 0.3:
            consider(_haar_try(d, rng))
            continue
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None:
            consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
