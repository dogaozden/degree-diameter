import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
#
# Start from the point-line incidence graph of PG(2, q), indices 0..m-1 for
# points and lines. Each old vertex has spare capacity s = d - q - 1.
#
#  * A-pencils: for each point P in S_A add a vertex joined to all q+1 lines
#    through P. Requires every line to contain at most s points of S_A.
#  * B-pencils: for each line j in S_B add a vertex joined to all q+1 points
#    on j. Requires every point to lie on at most s lines of S_B.
#  * Extra A-vertices: any line set T with |T| <= d that covers every point
#    (so each old point is within distance 2 of it) and that shares a line
#    with every other extra A-vertex. Each line may be used at most its
#    remaining capacity.
#  * Extra B-vertices: dual. A point set U with |U| <= d that meets every line,
#    pairwise intersecting, using remaining point capacity.
#
# Diameter stays 3: pencils and covers always meet, so every pair of new
# vertices is within distance 3 and every new-to-old pair is within 3.
# The parent's conic pencil set gives 394 for d=16. Here S_A and S_B are
# searched independently, and the extra covers are greedily packed into the
# capacity they leave free. The best verified graph is returned.
# ----------------------------------------------------------------------------


def _pg(q):
    """Return (m, point_lines, line_points) for PG(2, q); points and lines are indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, point_lines, line_points


def _masks(m, point_lines, line_points):
    """Return (linemask, ptmask): linemask[L] = bitmask of points on L, ptmask[P] = bitmask of lines through P."""
    linemask = [0] * m
    ptmask = [0] * m
    for P in range(m):
        for L in point_lines[P]:
            ptmask[P] |= 1 << L
    for L in range(m):
        for P in line_points[L]:
            linemask[L] |= 1 << P
    return linemask, ptmask


def _max_load(S, inc, m):
    """Largest number of elements of S that point to the same target, where inc[x] lists the targets of x."""
    load = [0] * m
    for x in S:
        for t in inc[x]:
            load[t] += 1
    return max(load, default=0)


def _random_set(m, s, inc, rng):
    """Random greedy set S with every target hit at most s times by the inc lists."""
    order = list(range(m))
    rng.shuffle(order)
    load = [0] * m
    S = []
    for x in order:
        if all(load[t] < s for t in inc[x]):
            S.append(x)
            for t in inc[x]:
                load[t] += 1
    return S


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point index set; an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _cover_family(m, sets, cap, d, rng, deadline, trials):
    """Greedily pack covers into remaining capacity.

    Items are 0..m-1. sets[x] is a bitmask over the universe (all m elements) covered by item x.
    Each chosen cover is a list of items of size <= d covering the whole universe, sharing an
    item with every earlier cover. An item may be used by at most cap[x] covers.
    """
    full = (1 << m) - 1
    cap = list(cap)
    chosen = []
    while time.monotonic() < deadline:
        found = None
        for _ in range(trials):
            T = []
            inT = set()
            covered = 0
            ok = True
            for prev in chosen:
                if any(x in inT for x in prev):
                    continue
                opts = [x for x in prev if cap[x] > 0]
                if not opts or len(T) >= d:
                    ok = False
                    break
                x = rng.choice(opts)
                T.append(x)
                inT.add(x)
                covered |= sets[x]
            if not ok:
                continue
            while covered != full and len(T) < d:
                bg = 0
                best = []
                for x in range(m):
                    if cap[x] > 0 and x not in inT:
                        g = (sets[x] & ~covered).bit_count()
                        if g > bg:
                            bg = g
                            best = [x]
                        elif g == bg and g > 0:
                            best.append(x)
                if bg == 0:
                    break
                x = rng.choice(best)
                T.append(x)
                inT.add(x)
                covered |= sets[x]
            if covered == full and len(T) <= d:
                found = T
                break
        if found is None:
            break
        for x in found:
            cap[x] -= 1
        chosen.append(found)
    return chosen


def _extend(m, point_lines, line_points, linemask, ptmask, d, s, SA, SB, rng, deadline):
    """Build the graph for pencil sets SA (points) and SB (lines), plus packed extra covers."""
    cl = [0] * m
    for P in SA:
        for L in point_lines[P]:
            cl[L] += 1
    cp = [0] * m
    for j in SB:
        for Q in line_points[j]:
            cp[Q] += 1
    capL = [s - c for c in cl]
    capP = [s - c for c in cp]
    extA = _cover_family(m, linemask, capL, d, rng, deadline, 8)
    extB = _cover_family(m, ptmask, capP, d, rng, deadline, 8)

    n = 2 * m + len(SA) + len(SB) + len(extA) + len(extB)
    E = []
    for P in range(m):
        for L in point_lines[P]:
            E.append((P, m + L))
    nxt = 2 * m
    for P in SA:
        for L in point_lines[P]:
            E.append((nxt, m + L))
        nxt += 1
    for j in SB:
        for Q in line_points[j]:
            E.append((Q, nxt))
        nxt += 1
    for T in extA:
        for L in T:
            E.append((nxt, m + L))
        nxt += 1
    for U in extB:
        for Q in U:
            E.append((Q, nxt))
        nxt += 1
    return n, E


def _best_arc_graph(q, d, rng, deadline):
    """Best graph of the arc-extended family for prime power q, or None."""
    s = d - q - 1
    if s < 0:
        return None
    m, point_lines, line_points = _pg(q)
    linemask, ptmask = _masks(m, point_lines, line_points)

    best = None

    def evaluate(SA, SB):
        nonlocal best
        g = _extend(m, point_lines, line_points, linemask, ptmask, d, s, SA, SB, rng, deadline)
        if best is None or g[0] > best[0]:
            best = g

    # Plain incidence graph (always valid for d >= q + 1).
    evaluate([], [])
    if s == 0:
        return best

    # Conic pencil set, as in the parent.
    if s >= 2:
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cs = _conic_set(q, index, lib.GF(q))
        if _max_load(cs, point_lines, m) <= s and _max_load(cs, line_points, m) <= s:
            evaluate(cs, cs)

    # Randomized search over independent A and B pencil sets.
    while time.monotonic() < deadline:
        SA = _random_set(m, s, point_lines, rng)
        SB = _random_set(m, s, line_points, rng)
        evaluate(SA, SB)
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
    deadline = start + 0.7 * time_limit
    arc_deadline = start + 0.5 * time_limit
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

    # Arc-extended projective plane graphs. Diameter 3, so valid for all D >= 3.
    if D >= 3:
        qs = [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)]
        for idx, q in enumerate(qs):
            now = time.monotonic()
            if now >= arc_deadline:
                break
            share = (arc_deadline - now) / (len(qs) - idx)
            g = _best_arc_graph(q, d, rng, now + share)
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
