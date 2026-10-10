import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction A (diameter 3): arc-extended projective plane incidence graphs.
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d-q-1.
# Pencils (the q+1 lines through a point) are the natural covers.
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


_LP = None  # line_points for the current q, set in _arc_extensions


def _arc_graph(m, edges, point_lines, S):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
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


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates from arc / conic pencil families for each prime power q with q + 1 <= d."""
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
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, S)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Construction B (diameter 3, NEW): packing of general line/point covers.
#
# A pencil is one kind of cover. Any set C of lines covering every point (every
# point lies on some line of C), with |C| <= d, can serve as the neighbourhood
# of a new vertex x on the point side. Dually, a set D of points covering every
# line can serve as the neighbourhood of a new vertex y on the line side.
#
# Validity conditions (the graph is PG(2,q) incidence plus these new vertices):
#   * two new x-vertices must share a line in their covers (distance 2);
#   * two new y-vertices must share a point in their covers (distance 2);
#   * each old line receives at most s = d-q-1 new x-edges, each old point at
#     most s new y-edges (so old degrees stay <= d);
#   * x reaches every old point in 2 (cover), every old line in 3 (through a
#     point of the line and a cover line), and every y in 3 (a cover line
#     meets a point of D_y because D_y covers all lines); symmetrically for y.
# Hence the diameter stays 3 and the graph stays bipartite (x and the points
# are one side, y and the lines the other). Order is 2m + |FX| + |FY|.
# Pencils are covers of size q+1, so this family contains the arc construction;
# larger covers can use spare degree that pencils cannot.
# ----------------------------------------------------------------------------

def _random_cover(nA, cov, inc, load, s, d, rng, beta):
    """Greedy random cover of range(nA) using B-elements with load < s, size <= d, or None."""
    uncovered = set(range(nA))
    chosen = []
    cset = set()
    while uncovered:
        if len(chosen) >= d:
            return None
        a = rng.choice(list(uncovered))
        cands = [b for b in cov[a] if load[b] < s and b not in cset]
        if not cands:
            return None
        best, best_score = None, None
        for b in cands:
            gain = sum(1 for x in inc[b] if x in uncovered)
            score = gain + beta * load[b] + 0.5 * rng.random()
            if best_score is None or score > best_score:
                best, best_score = b, score
        chosen.append(best)
        cset.add(best)
        uncovered.difference_update(inc[best])
    return chosen


def _cover_family(nA, cov, inc, s, d, rng, deadline):
    """Pairwise-intersecting family of covers with element loads <= s; returns the largest found."""
    best = []
    nB = len(inc)
    while time.monotonic() < deadline:
        load = [0] * nB
        fam = []
        sets = []
        beta = rng.choice([0.0, 0.5, 1.0, 2.0])
        fails = 0
        while fails < 40 and time.monotonic() < deadline:
            c = _random_cover(nA, cov, inc, load, s, d, rng, beta)
            if c is None:
                fails += 1
                continue
            cs = set(c)
            if not all(not cs.isdisjoint(o) for o in sets):
                fails += 1
                continue
            fam.append(c)
            sets.append(cs)
            for b in c:
                load[b] += 1
            fails = 0
        if len(fam) > len(best):
            best = fam
    return best


def _cover_graph(m, edges, FX, FY):
    """Assemble PG(2,q) incidence plus new x-vertices (on lines FX) and new y-vertices (on points FY)."""
    nx, ny = len(FX), len(FY)
    n = 2 * m + nx + ny
    E = list(edges)
    for t, C in enumerate(FX):
        x = 2 * m + t
        for L in C:
            E.append((x, m + L))
    for t, D in enumerate(FY):
        y = 2 * m + nx + t
        for P in D:
            E.append((P, y))
    return n, E


def _cover_extensions(d, deadline, rng):
    """Return (n, edges) candidates from cover packings for each prime power q with q + 1 < d."""
    out = []
    qs = [q for q in range(2, min(d - 1, 23) + 1)
          if lib.is_prime_power(q) and d - q - 1 >= 1]
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        # X side: cover all points by lines. cov[point] = lines through it, inc[line] = its points.
        FX = _cover_family(m, point_lines, line_points, s, d, rng, now + share / 2)
        # Y side (dual): cover all lines by points. cov[line] = its points, inc[point] = lines through it.
        FY = _cover_family(m, line_points, point_lines, s, d, rng, now + share)
        if not FX and not FY:
            continue
        n_c, e_c = _cover_graph(m, edges, FX, FY)
        out.append((n_c, e_c))
    return out


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
        # Construction A: arc-extended pencil families (diameter 3).
        arc = _arc_extensions(d, start + 0.2 * time_limit, random.Random(seed * 7919 + d))
        arc.sort(key=lambda t: -t[0])
        for n_c, e_c in arc:
            if n_c > best_n:
                consider(n_c, e_c)

        # Construction B (new): general cover packings (diameter 3).
        cov = _cover_extensions(d, start + 0.45 * time_limit, random.Random(seed * 104729 + d))
        cov.sort(key=lambda t: -t[0])
        for n_c, e_c in cov:
            if n_c > best_n:
                consider(n_c, e_c)

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
