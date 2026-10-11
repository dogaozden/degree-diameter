import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# D = 3, family 1: PG(2, q) incidence graph plus "arc" extension.
#
# For q with q + 1 <= d and spare s = d - q - 1, pick a set S of points.
# Add one A-vertex per point P in S (joined to the q+1 lines through P) and
# one B-vertex per line j in S (joined to the q+1 points on j). Every new
# vertex is a twin of an old one, so the diameter stays 3. Degrees stay <= d
# iff every line holds <= s points of S and every point lies on <= s lines
# indexed by S. The conic (plus nucleus for even q) is a strong choice of S.
# ----------------------------------------------------------------------------

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
    """Randomized greedy S with all loads <= s; returns the largest found."""
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


def _arc_graph(m, edges, point_lines, line_points, S):
    """PG incidence graph plus an A-vertex per S-point and a B-vertex per S-line."""
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
    return n, E


def _pg_arc_best(d, deadline, rng):
    """Best arc-extended PG(2, q) graph over prime powers q with q + 1 <= d. Returns (n, edges) or (0, None)."""
    best_n, best_e = 0, None
    for q in range(2, d):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        n0, edges = lib.projective_plane_incidence(q)
        m = n0 // 2
        pts = lib.projective_points(q)
        point_lines = [[] for _ in range(m)]
        line_points = [[] for _ in range(m)]
        for u, v in edges:
            point_lines[u].append(v - m)
            line_points[v - m].append(u)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 30, deadline))
        if s >= 2:
            F = lib.GF(q)
            index = {p: i for i, p in enumerate(pts)}
            cs = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
            if q % 2 == 0:
                cs.append(index[(0, 1, 0)])
            cands.append(cs)
        S = []
        for cand in sorted(cands, key=len, reverse=True):
            if _loads_ok(cand, s, m, point_lines, line_points):
                S = cand
                break
        n, E = _arc_graph(m, edges, point_lines, line_points, S)
        if n > best_n and lib.is_valid(n, E, d, 3):
            best_n, best_e = n, E
    return best_n, best_e


# ----------------------------------------------------------------------------
# D = 3, family 2: Haar graphs from difference covers.
#
# H(m, S): a_i ~ b_{i+s} for s in S, |S| = d, order 2m. If S - S = Z_m then
# every pair is within distance 3, so the graph has diameter 3. We search for
# a cover of size d for as large m as possible (order 2m must beat the
# current best). Moves: focused moves create an uncovered difference g, random
# moves otherwise. Metropolis acceptance with a reheating schedule.
# ----------------------------------------------------------------------------

def _cover_anneal(k, m, rng, deadline):
    """Find S in Z_m, |S| = k, with S - S = Z_m. Returns sorted S or None on timeout."""
    if k < 2 or m < k:
        return None
    S = rng.sample(range(m), k)
    in_s = set(S)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    uncov = [g for g in range(1, m) if cnt[g] == 0]
    cycle = 300000
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0:
            if time.monotonic() > deadline:
                return None
            uncov = [g for g in range(1, m) if cnt[g] == 0]
        phase = (it % cycle) / cycle
        T = 0.6 * (0.15 / 0.6) ** phase
        g = None
        if uncov and rng.random() < 0.7:
            g0 = uncov[rng.randrange(len(uncov))]
            if cnt[g0] == 0:
                g = g0
        if g is not None:
            j = rng.randrange(k)
            s = S[j]
            y = (s + g) % m if rng.random() < 0.5 else (s - g) % m
            i = rng.randrange(k - 1)
            if i >= j:
                i += 1
            x = S[i]
        else:
            i = rng.randrange(k)
            x = S[i]
            y = rng.randrange(m)
        if y in in_s:
            continue
        others = S[:i] + S[i + 1:]
        delta = 0
        for s in others:
            g1 = (x - s) % m
            cnt[g1] -= 1
            if cnt[g1] == 0:
                delta += 1
            g1 = (s - x) % m
            cnt[g1] -= 1
            if cnt[g1] == 0:
                delta += 1
        for s in others:
            g1 = (y - s) % m
            if cnt[g1] == 0:
                delta -= 1
            cnt[g1] += 1
            g1 = (s - y) % m
            if cnt[g1] == 0:
                delta -= 1
            cnt[g1] += 1
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            in_s.discard(x)
            in_s.add(y)
            unc += delta
        else:
            for s in others:
                cnt[(y - s) % m] -= 1
                cnt[(s - y) % m] -= 1
            for s in others:
                cnt[(x - s) % m] += 1
                cnt[(s - x) % m] += 1
    return sorted(S)


def _haar_climb(d, m_start, m_max, deadline, rng):
    """Climb m upward while difference covers are found. Returns (m, S) or None."""
    best = None
    m = m_start
    while m <= m_max and time.monotonic() < deadline:
        S = _cover_anneal(d, m, rng, deadline)
        if S is None:
            break
        best = (m, S)
        m += 1
    return best


# ----------------------------------------------------------------------------
# D >= 4: generalized quadrangle W(q) incidence graph (diameter 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * float(time_limit), 42.0)
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 31 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if e is not None and n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if D >= 3 and d >= 3:
        n, e = _pg_arc_best(d, start + 0.25 * budget, rng)
        consider(n, e)

    if D == 3 and d >= 2:
        mstart = max(d, best_n // 2 + 1)
        mmax = d * (d - 1) + 1
        if mstart <= mmax:
            res = _haar_climb(d, mstart, mmax, deadline, rng)
            if res is not None:
                m, S = res
                n, e = lib.haar_graph(m, S)
                consider(n, e)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, list(best_e)
