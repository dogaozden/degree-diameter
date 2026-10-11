import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction: cover-family extension of PG(2, q) incidence graphs (D = 3).
#
# Start from PG(2,q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so it has spare capacity s = d - q - 1.
#
# A new "point-side" vertex X is joined to a set T of lines. For the diameter to
# stay 3 it is enough that:
#   (a) T covers all points (every point lies on a line of T), and
#   (b) T meets every other point-side vertex's line set (common neighbour).
# Each line can take at most s new edges. Point-side and line-side families are
# independent: A-sets use only line capacity, B-sets (dual) use only point
# capacity. A new point-side vertex and a new line-side vertex are then always
# within distance 3, and old-to-new distances are within 3 by the covering.
#
# The arc (conic) construction is one such family: s pencils at a set of points
# with no three collinear. This program keeps that family as the start and runs
# a randomized greedy search that tries to add further covers (or replace
# members) to get more new vertices. The result is never smaller than the arc
# construction, and every candidate is checked with lib.is_valid.
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


def _mask(elems):
    """Bitmask with bit e set for each e in elems."""
    x = 0
    for e in elems:
        x |= 1 << e
    return x


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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear, as point indices."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _greedy_cover(m, cover, cap, fam_masks, dmax, rng):
    """Greedy cover of all targets by elements with capacity left, hitting every mask in fam_masks.

    cover[e] is a bitmask of the targets covered by element e. Returns a list of elements, or None.
    """
    unc = (1 << m) - 1
    unhit = list(fam_masks)
    chosen = []
    used = set()
    while unc or unhit:
        if len(chosen) >= dmax:
            return None
        best, best_e = -1.0, -1
        for e in range(m):
            if cap[e] <= 0 or e in used:
                continue
            bit = 1 << e
            g = (cover[e] & unc).bit_count()
            h = 0
            for f in unhit:
                if f & bit:
                    h += 1
            sc = 2.0 * g + 5.0 * h + 2.0 * rng.random()
            if sc > best:
                best, best_e = sc, e
        if best_e < 0:
            return None
        chosen.append(best_e)
        used.add(best_e)
        bit = 1 << best_e
        unc &= ~cover[best_e]
        unhit = [f for f in unhit if not f & bit]
    return chosen


def _family_search(m, cover, s, dmax, init, rng, deadline, stall_limit):
    """Randomized search for a large family of covers, each element used at most s times.

    init: starting family (lists of elements), assumed valid. Returns the largest family seen.
    Members are pairwise intersecting covers. A failed step may drop a random member.
    """
    cap = [s] * m
    cur = []
    for T in init:
        cur.append((list(T), _mask(T)))
        for e in T:
            cap[e] -= 1
    best = [list(T) for T, _ in cur]
    fails = 0
    while fails < stall_limit and time.monotonic() < deadline:
        masks = [mk for _, mk in cur]
        T = None
        for _ in range(3):
            T = _greedy_cover(m, cover, cap, masks, dmax, rng)
            if T is not None:
                break
        if T is not None:
            cur.append((T, _mask(T)))
            for e in T:
                cap[e] -= 1
            fails = 0
            if len(cur) > len(best):
                best = [list(X) for X, _ in cur]
        else:
            fails += 1
            if cur and rng.random() < 0.25:
                T0, _ = cur.pop(rng.randrange(len(cur)))
                for e in T0:
                    cap[e] += 1
    return best


def _family_graph(q, d, deadline, rng):
    """Build PG(2,q) incidence plus new point-side and line-side vertices from cover families."""
    s = d - q - 1
    if s < 2:
        return None
    m, edges, point_lines, line_points, index, pts = _pg_data(q)
    F = lib.GF(q)
    S = _conic_set(q, index, F)
    init_A, init_B = [], []
    if _loads_ok(S, s, m, point_lines, line_points):
        init_A = [list(point_lines[P]) for P in S]    # pencils: lines through P
        init_B = [list(line_points[j]) for j in S]    # dual pencils: points on line j
    line_cov = [_mask(line_points[L]) for L in range(m)]   # element = line, covers points
    pt_cov = [_mask(point_lines[P]) for P in range(m)]     # element = point, covers lines
    now = time.monotonic()
    half = now + 0.5 * max(0.0, deadline - now)
    famA = _family_search(m, line_cov, s, d, init_A, rng, half, 60)
    famB = _family_search(m, pt_cov, s, d, init_B, rng, deadline, 60)
    n = 2 * m + len(famA) + len(famB)
    E = list(edges)
    x = 2 * m
    for T in famA:
        for L in T:
            E.append((x, m + L))
        x += 1
    for U in famB:
        for P in U:
            E.append((P, x))
        x += 1
    return n, E


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

    # Cover-family extension of PG(2,q) (diameter 3, so valid for all D >= 3).
    if D >= 3:
        qs = [q for q in range(min(d - 3, 23), 1, -1) if lib.is_prime_power(q)][:3]
        fam_end = start + 0.5 * time_limit
        for idx, q in enumerate(qs):
            now = time.monotonic()
            share = max(0.0, fam_end - now) / (len(qs) - idx)
            try:
                g = _family_graph(q, d, now + share, random.Random(seed * 131 + q))
            except Exception:
                g = None
            if g is not None:
                consider(g[0], g[1])

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
