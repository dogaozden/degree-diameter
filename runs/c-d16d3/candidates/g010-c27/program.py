import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Weighted extension of projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q): points 0..m-1, lines m..2m-1.
# Spare capacity s = d - q - 1 on every old vertex.
#
# A-side: a weight w_A[P] >= 0 on points means w_A[P] new vertices, each joined to
#   all q+1 lines through P. Line L then gains sum_{P on L} w_A[P] degree, which
#   must be <= s.
# B-side: a weight w_B[L] >= 0 on lines means w_B[L] new vertices, each joined to
#   all q+1 points on L. Point Q gains sum_{L through Q} w_B[L] degree, <= s.
#
# Diameter stays 3 for any such weights (checked by lib.is_valid anyway), since
# two same-side new vertices share a neighbour and a new A and a new B vertex are
# joined through the point (line through P) meeting the line of B. So the only
# constraint is the load condition, and the order is 2m + sum(w_A) + sum(w_B).
#
# The weight problem is maximised by iterated local search: random greedy fill,
# then remove a few copies and refill, keeping plateau moves. The conic (an
# oval, a 2-arc for odd q) is used as the start when feasible, so the search
# never does worse than the conic construction.
# ----------------------------------------------------------------------------

def _pg_data(q):
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


def _conic(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _feasible_init(init, cons, s, n_con):
    """Return the constraint loads of init if all are <= s, else None."""
    load = [0] * n_con
    for i, x in enumerate(init):
        if x:
            for c in cons[i]:
                load[c] += x
    if max(load, default=0) > s:
        return None
    return load


def _ils_weights(n_items, cons, n_con, s, rng, deadline, init=None):
    """Maximise sum(w) with w >= 0 integer, subject to sum_{i: c in cons[i]} w[i] <= s for each constraint c.

    Returns (best_w, best_total).
    """
    def fill(w, load, order):
        for i in order:
            cs = cons[i]
            if not cs:
                continue
            while all(load[c] < s for c in cs):
                w[i] += 1
                for c in cs:
                    load[c] += 1

    w = [0] * n_items
    load = [0] * n_con
    if init is not None:
        l0 = _feasible_init(init, cons, s, n_con)
        if l0 is not None:
            w = list(init)
            load = l0
    order = list(range(n_items))
    rng.shuffle(order)
    fill(w, load, order)
    total = sum(w)
    best_w, best = w[:], total

    while time.monotonic() < deadline:
        w2 = w[:]
        load2 = load[:]
        for _ in range(rng.randint(1, 4)):
            cand = [i for i in range(n_items) if w2[i] > 0]
            if not cand:
                break
            i = rng.choice(cand)
            w2[i] -= 1
            for c in cons[i]:
                load2[c] -= 1
        order = list(range(n_items))
        rng.shuffle(order)
        fill(w2, load2, order)
        t2 = sum(w2)
        if t2 >= total:
            w, load, total = w2, load2, t2
            if total > best:
                best, best_w = total, w[:]
    return best_w, best


def _arc_graph(m, edges, point_lines, line_points, wA, wB):
    """Old PG incidence plus wA[P] A-vertices per point P and wB[L] B-vertices per line L."""
    n = 2 * m
    E = list(edges)
    for P, w in enumerate(wA):
        for _ in range(w):
            x = n
            n += 1
            for L in point_lines[P]:
                E.append((x, m + L))
    for L, w in enumerate(wB):
        for _ in range(w):
            y = n
            n += 1
            for Q in line_points[L]:
                E.append((Q, y))
    return n, E


def _extensions(d, deadline, rng):
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now >= deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        if s <= 0:
            out.append((2 * m, list(edges)))
            continue
        F = lib.GF(q)
        S = _conic(q, index, F)
        init = [0] * m
        for i in S:
            init[i] = 1
        share = (deadline - now) / (len(qs) - idx) / 2
        wA, _ = _ils_weights(m, point_lines, m, s, rng, time.monotonic() + share, init)
        wB, _ = _ils_weights(m, line_points, m, s, rng, time.monotonic() + share, init)
        out.append(_arc_graph(m, edges, point_lines, line_points, wA, wB))
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

    # Weighted projective-plane extensions. Diameter 3, so valid for all D >= 3.
    if D >= 3:
        arc_deadline = start + (0.7 if D == 3 else 0.4) * time_limit
        for n_c, e_c in _extensions(d, arc_deadline, random.Random(seed * 7919 + d)):
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
