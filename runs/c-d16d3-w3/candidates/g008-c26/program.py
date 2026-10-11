import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane extensions (diameter 3).
#
# Start from the incidence graph of PG(2, q): points 0..m-1, lines m..2m-1.
# Every old vertex has degree q+1, so with d >= q+1 the spare is s = d-q-1.
#
# A-side: a family of line-sets N(x), one new vertex x per set, joined to
#         every line in N(x). Requirements:
#           (a) N(x) covers all points (every point lies on a line of N(x)),
#           (b) any two A-sets share a line (so A-vertices are at distance 2),
#           (c) every line lies in at most s A-sets (line degree q+1+load <= d),
#           (d) |N(x)| <= d.
# B-side: the dual. Point-sets N(y) covering all lines, pairwise sharing a
#         point, each point in at most s B-sets, size <= d.
#
# Why these suffice: an A-vertex reaches every point in 2 steps (cover), every
# line in <= 3 (any two lines meet), and every B-vertex in 3 (each line of N(x)
# contains a point of N(y) because N(y) covers all lines). Bipartiteness holds:
# A-vertices sit on the point side, B-vertices on the line side.
#
# Pencils (all lines through one point) are the easy covers, and a family of
# pencils is an arc of PG(2,q), so it is capped at q+1 = 14 for q = 13. The
# generic search below uses covers that are not pencils, which can give more
# sets. Each pair of sets must share a distinct line, so |family| <= about
# (d+1) for the size-d covers.
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


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s entries of S (repeats counted), where entry x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _multi_side(m, s, nbr, rng, deadline):
    """Iterated greedy over multisets of pencil centres: every target is hit <= s times."""
    order = list(range(m))

    def fill(S, load):
        rng.shuffle(order)
        for x in order:
            nb = nbr[x]
            while all(load[t] < s for t in nb):
                S.append(x)
                for t in nb:
                    load[t] += 1
        return S

    cur = fill([], [0] * m)
    best = list(cur)
    while time.monotonic() < deadline:
        S = list(cur)
        load = [0] * m
        for x in S:
            for t in nbr[x]:
                load[t] += 1
        for _ in range(min(rng.randint(1, 3), len(S))):
            i = rng.randrange(len(S))
            x = S.pop(i)
            for t in nbr[x]:
                load[t] -= 1
        S = fill(S, load)
        if len(S) >= len(cur):
            cur = S
            if len(cur) > len(best):
                best = list(cur)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA entry and one new B-vertex per SB entry."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Pencil-based candidates (arc-type multisets) for each prime power q with q + 1 <= d."""
    out = []
    qs = sorted((q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)), reverse=True)
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        per_side = (deadline - now) / (2 * (len(qs) - idx))
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _multi_side(m, s, point_lines, rng, time.monotonic() + per_side)
        SB = _multi_side(m, s, line_points, rng, time.monotonic() + per_side)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Generic cover families (the new part).
#
# cov[e] lists the targets covered by element e. For the A-side, elements are
# lines and targets are points; for the B-side, elements are points and
# targets are lines. A family is a list of element-sets, each covering all
# targets, pairwise sharing an element, with every element used at most s times.
# ----------------------------------------------------------------------------

def _try_cover(m, s, dmax, cov, ntar, load, fam, inc, rng):
    """Randomized greedy for one new cover. Returns a list of elements, or None on failure."""
    covered = [False] * ntar
    nuncov = ntar
    hit = [False] * len(fam)
    nunhit = len(fam)
    inN = [False] * m
    chosen = []
    W = rng.choice([1, 2, 3])
    noise = rng.random() * 0.99
    for _ in range(dmax):
        if nuncov == 0 and nunhit == 0:
            return chosen
        best = -1
        bestsc = -1e18
        for e in range(m):
            if inN[e] or load[e] >= s:
                continue
            g = 0
            for t in cov[e]:
                if not covered[t]:
                    g += 1
            h = 0
            for j in inc[e]:
                if not hit[j]:
                    h += 1
            sc = g + W * h + noise * rng.random()
            if sc > bestsc:
                best = e
                bestsc = sc
        if best < 0:
            return None
        chosen.append(best)
        inN[best] = True
        for t in cov[best]:
            if not covered[t]:
                covered[t] = True
                nuncov -= 1
        for j in inc[best]:
            if not hit[j]:
                hit[j] = True
                nunhit -= 1
    if nuncov == 0 and nunhit == 0:
        return chosen
    return None


def _grow_family(m, s, dmax, cov, ntar, rng, deadline, fails_limit=300):
    """Repeatedly find new covers that pairwise intersect the family and respect load <= s."""
    load = [0] * m
    inc = [[] for _ in range(m)]
    fam = []
    fails = 0
    while time.monotonic() < deadline and fails < fails_limit:
        N = _try_cover(m, s, dmax, cov, ntar, load, fam, inc, rng)
        if N is None:
            fails += 1
            continue
        j = len(fam)
        fam.append(N)
        for e in N:
            load[e] += 1
            inc[e].append(j)
        fails = 0
    return fam


def _gen_graph(m, edges, famA, famB):
    """PG(2,q) incidence plus an A-vertex per line-set and a B-vertex per point-set."""
    na = len(famA)
    n = 2 * m + na + len(famB)
    E = list(edges)
    for t, N in enumerate(famA):
        x = 2 * m + t
        for L in N:
            E.append((x, m + L))
    for t, N in enumerate(famB):
        y = 2 * m + na + t
        for P in N:
            E.append((P, y))
    return n, E


def _generic_extensions(d, deadline, rng):
    """Generic cover-family candidates for each prime power q with q + 1 <= d."""
    out = []
    qs = sorted((q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)), reverse=True)
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        per_side = (deadline - now) / (2 * (len(qs) - idx))
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        # A-side: elements are lines, covering the points on each line.
        famA = _grow_family(m, s, d, line_points, m, rng, time.monotonic() + per_side)
        # B-side: elements are points, covering the lines through each point.
        famB = _grow_family(m, s, d, point_lines, m, rng, time.monotonic() + per_side)
        out.append(_gen_graph(m, edges, famA, famB))
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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
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

    if D >= 3:
        # Pencil-based arc candidates (quick baseline).
        arc_deadline = start + (0.15 if D == 3 else 0.10) * time_limit
        for n_c, e_c in _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

        # Generic cover families: the main search for D = 3.
        gen_deadline = start + (0.70 if D == 3 else 0.35) * time_limit
        for n_c, e_c in _generic_extensions(d, gen_deadline, random.Random(seed * 104729 + d)):
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Voltage-lift annealing for D != 3. Larger bases for D >= 5.
    if D != 3:
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
