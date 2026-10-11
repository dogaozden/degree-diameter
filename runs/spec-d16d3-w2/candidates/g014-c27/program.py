import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc helpers (D = 3 fallback / baseline)
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
    return n, E


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
# D = 3 via Haar graphs from difference covers.
#
# H(m, S) has parts Z_m and Z_m with a_i ~ b_{i+s} for s in S. It is |S|-regular
# and bipartite. Diameter 3 holds when S - S = Z_m (a difference cover), so the
# order is 2m with m <= k(k-1)+1.
#
# Improvement: instead of climbing m from a low start, aim directly at the
# first m that beats the current best (m = best_n // 2 + 1), and search there.
# The annealer proposes moves that cover a random currently-uncovered difference
# g by placing an element at S[j] + g, which is much more efficient than random
# element replacement.
# ----------------------------------------------------------------------------

def _cover_anneal(k, m, rng, deadline):
    """Find S subset of Z_m with |S| = k and S - S = Z_m, using restarted targeted annealing. Returns sorted S or None."""
    if m < k:
        return None
    while time.monotonic() < deadline:
        S = rng.sample(range(m), k)
        in_s = set(S)
        cnt = [0] * m
        for a in S:
            for b in S:
                if a != b:
                    cnt[(a - b) % m] += 1
        unc = sum(1 for g in range(1, m) if cnt[g] == 0)
        T = 0.6
        steps = 0
        limit = 300000
        while unc > 0 and steps < limit:
            steps += 1
            if (steps & 1023) == 0 and time.monotonic() > deadline:
                return None
            # Pick a random uncovered nonzero difference g.
            g = rng.randrange(1, m)
            while cnt[g] != 0:
                g = rng.randrange(1, m)
            i = rng.randrange(k)
            j = rng.randrange(k)
            if j == i:
                continue
            x = S[i]
            y = (S[j] + g) % m
            if y in in_s:
                continue
            others = S[:i] + S[i + 1:]
            delta = 0
            # Remove x's differences.
            for s in others:
                h = (x - s) % m
                cnt[h] -= 1
                if cnt[h] == 0:
                    delta += 1
                h = (s - x) % m
                cnt[h] -= 1
                if cnt[h] == 0:
                    delta += 1
            # Add y's differences.
            for s in others:
                h = (y - s) % m
                if cnt[h] == 0:
                    delta -= 1
                cnt[h] += 1
                h = (s - y) % m
                if cnt[h] == 0:
                    delta -= 1
                cnt[h] += 1
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
            T = max(0.08, T * 0.99998)
        if unc == 0:
            return sorted(S)
    return None


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
    budget = min(0.8 * float(time_limit), 45.0)
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
        # Baseline: arc-extended projective plane.
        cands = _arc_candidates(d, start + 0.25 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        if cands:
            consider(cands[0][0], cands[0][1])

        # Main: aim directly at the first Haar graph that beats the current best.
        if d >= 2:
            k = d
            mmax = k * (k - 1) + 1
            m = max(k, best_n // 2 + 1)
            while m <= mmax and time.monotonic() < deadline:
                S = _cover_anneal(k, m, rng, deadline)
                if S is None:
                    break
                n, E = lib.haar_graph(m, S)
                consider(n, E)
                m += 1

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
