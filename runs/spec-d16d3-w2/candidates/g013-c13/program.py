import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc construction (D = 3)
# ----------------------------------------------------------------------------

def _pg_incidence(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points 0..m-1, lines indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


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
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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


def _conic_set(q, index):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Incidence graph of PG(2,q) plus, per element of S, an A-vertex and a B-vertex."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _arc_candidates(d, deadline, rng):
    """For each prime power q with q + 1 <= d, build the best arc-extended PG(2,q) graph."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points = _pg_incidence(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 60, deadline))
        if s >= 2:
            cs = _conic_set(q, index)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Haar graphs over abelian groups Z_a x Z_b (D = 3)
#
# H(G, S): parts A = G, B = G, a_x ~ b_{x+s} for s in S. If S - S = G then
# every pair of same-side vertices is at distance 2 and every mixed pair is
# at distance <= 3, so the diameter is 3. The order is 2|G|.
# Search: annealing on the number of uncovered nonzero differences, with
# focused moves that cover a randomly chosen uncovered difference.
# ----------------------------------------------------------------------------

_TABLE_CACHE = {}


def _tables(a, b):
    """Addition and subtraction tables for Z_a x Z_b; element u*b+v codes (u, v)."""
    key = (a, b)
    if key in _TABLE_CACHE:
        return _TABLE_CACHE[key]
    m = a * b
    add = [[0] * m for _ in range(m)]
    sub = [[0] * m for _ in range(m)]
    for x in range(m):
        ux, vx = divmod(x, b)
        ra, rs = add[x], sub[x]
        for y in range(m):
            uy, vy = divmod(y, b)
            ra[y] = ((ux + uy) % a) * b + (vx + vy) % b
            rs[y] = ((ux - uy) % a) * b + (vx - vy) % b
    _TABLE_CACHE[key] = (add, sub)
    return add, sub


def _group_shapes(m):
    """Abelian groups of order m with rank <= 2: cyclic first, then Z_a x Z_b with a | b, a >= 2."""
    shapes = [(1, m)]
    for a in range(2, math.isqrt(m) + 1):
        if m % a == 0 and (m // a) % a == 0:
            shapes.append((a, m // a))
    return shapes


def _cover(k, a, b, rng, deadline):
    """Find S in Z_a x Z_b with |S| = k and S - S = whole group. Returns sorted S (codes) or None."""
    m = a * b
    if m < k:
        return None
    add, sub = _tables(a, b)
    S = rng.sample(range(m), k)
    in_s = set(S)
    cnt = [0] * m
    for x in S:
        for y in S:
            if x != y:
                cnt[sub[x][y]] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    it = 0
    epoch = 60000
    while unc > 0:
        it += 1
        if (it & 511) == 0 and time.monotonic() > deadline:
            return None
        T = 0.6 * (0.2 ** ((it % epoch) / epoch))
        # Focused move: pick an uncovered difference g and make it appear.
        g = rng.randrange(1, m)
        while cnt[g] > 0:
            g = rng.randrange(1, m)
        i = rng.randrange(k)
        j = rng.randrange(k - 1)
        if j >= i:
            j += 1
        s = S[j]
        y = add[s][g]          # now y - s = g
        x = S[i]
        if y in in_s:
            continue
        others = [S[t] for t in range(k) if t != i]
        delta = 0
        # Remove differences involving x.
        for t in others:
            h = sub[x][t]
            cnt[h] -= 1
            if cnt[h] == 0:
                delta += 1
            h = sub[t][x]
            cnt[h] -= 1
            if cnt[h] == 0:
                delta += 1
        # Add differences involving y.
        for t in others:
            h = sub[y][t]
            if cnt[h] == 0:
                delta -= 1
            cnt[h] += 1
            h = sub[t][y]
            if cnt[h] == 0:
                delta -= 1
            cnt[h] += 1
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            in_s.discard(x)
            in_s.add(y)
            unc += delta
        else:
            for t in others:
                cnt[sub[y][t]] -= 1
                cnt[sub[t][y]] -= 1
            for t in others:
                cnt[sub[x][t]] += 1
                cnt[sub[t][x]] += 1
    return sorted(S)


def _haar_edges(a, b, S):
    """Edges of the Haar-type graph over Z_a x Z_b: a_x ~ b_{x+s}."""
    m = a * b
    add, _ = _tables(a, b)
    E = [(x, m + add[x][s]) for x in range(m) for s in S]
    return 2 * m, E


def _search_haar(k, rng, deadline, d, D):
    """Climb m upward through difference covers of size k; return the largest valid (n, edges) or None."""
    mmax = k * (k - 1) + 1
    m = max(k, int(0.8 * mmax))
    best = None
    while m <= mmax and time.monotonic() < deadline:
        for a, b in _group_shapes(m):
            now = time.monotonic()
            if now >= deadline:
                break
            remaining = deadline - now
            slice_ = max(0.4, min(3.0, remaining / 6.0))
            S = _cover(k, a, b, rng, min(deadline, now + slice_))
            if S is not None:
                n, E = _haar_edges(a, b, S)
                if (best is None or n > best[0]) and lib.is_valid(n, E, d, D):
                    best = (n, E)
                break
        m += 1
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4)
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * float(time_limit), 46.0)
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 17 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D == 3:
        if d >= 2:
            # Arc-extended projective plane (fast, gives the record for d = 16).
            cands = _arc_candidates(d, start + 0.2 * budget, random.Random(seed * 7919 + d))
            cands.sort(key=lambda t: -t[0])
            for n_c, E_c, _side in cands[:1]:
                consider(n_c, E_c)
            # Main search: difference covers in abelian groups of order m, aiming above the record.
            mmax = d * (d - 1) + 1
            if mmax <= 400:
                res = _search_haar(d, rng, deadline - 0.5, d, D)
                if res is not None:
                    consider(res[0], res[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
