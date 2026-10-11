import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc helpers (D = 3 fallback, reproduces the 394 record for d=16)
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
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
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
# NEW helper: targeted tabu search for difference covers.
#
# A set S of size k in Z_m with S - S = Z_m gives the Haar graph H(m, S), a
# k-regular bipartite graph on 2m vertices with diameter 3. The search keeps k
# elements and minimizes the number of uncovered nonzero differences. Each step
# picks an uncovered difference g and proposes new elements y = s +/- g, which
# covers g directly. It then evaluates every swap that puts y in for some x in S
# and takes the best non-tabu one. Stagnation triggers a random perturbation.
# ----------------------------------------------------------------------------

def _swap(i, y, S, in_s, cnt, m):
    """Replace S[i] by y, updating ordered-difference counts; return change in #uncovered differences."""
    x = S[i]
    k = len(S)
    delta = 0
    for j in range(k):
        if j != i:
            s = S[j]
            g = (x - s) % m
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
            g = (s - x) % m
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
    for j in range(k):
        if j != i:
            s = S[j]
            g = (y - s) % m
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
            g = (s - y) % m
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
    S[i] = y
    in_s[x] = False
    in_s[y] = True
    return delta


def _cover_tabu(k, m, rng, deadline):
    """Find S subset of Z_m, |S| = k, with S - S = Z_m. Returns sorted S, or None at deadline."""
    if m < k or k < 2:
        return None
    if m == k:
        return list(range(m))
    S = rng.sample(range(m), k)
    in_s = [False] * m
    for s in S:
        in_s[s] = True
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    tabu = [0] * m
    best_unc = unc
    stall = 0
    it = 0
    while unc > 0:
        it += 1
        if (it & 15) == 0 and time.monotonic() > deadline:
            return None
        gs = [g for g in range(1, m) if cnt[g] == 0]
        g = rng.choice(gs)
        ys = set()
        for s in S:
            ys.add((s + g) % m)
            ys.add((s - g) % m)
        ys = [y for y in ys if not in_s[y]]
        rng.shuffle(ys)
        ys = ys[:8]
        best = None
        bestd = None
        for y in ys:
            for i in range(k):
                x = S[i]
                d = _swap(i, y, S, in_s, cnt, m)
                _swap(i, x, S, in_s, cnt, m)
                if tabu[y] > it and unc + d >= best_unc:
                    continue
                if bestd is None or d < bestd or (d == bestd and rng.random() < 0.3):
                    best = (i, y)
                    bestd = d
        if best is None:
            stall += 1
            continue
        i, y = best
        x = S[i]
        unc += _swap(i, y, S, in_s, cnt, m)
        tabu[x] = it + 5 + rng.randrange(max(1, k // 2))
        if unc < best_unc:
            best_unc = unc
            stall = 0
        else:
            stall += 1
        if stall > 300:
            for _ in range(3):
                i2 = rng.randrange(k)
                y2 = rng.randrange(m)
                if in_s[y2]:
                    continue
                x2 = S[i2]
                unc += _swap(i2, y2, S, in_s, cnt, m)
                tabu[x2] = it + 10
            stall = 0
            best_unc = unc
    return sorted(S)


def _haar_search(k, m0, rng, deadline):
    """Try m = m0, m0+1, ... with the difference-cover search. Returns (m, S) for the largest success, or None."""
    mmax = k * (k - 1) + 1
    best = None
    fails = 0
    m = m0
    while m <= mmax and time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        slice_ = max(1.0, 0.5 * remaining)
        S = _cover_tabu(k, m, rng, min(deadline, time.monotonic() + slice_))
        if S is not None:
            best = (m, S)
            fails = 0
        else:
            fails += 1
            if fails >= 2:
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
    budget = min(0.75 * float(time_limit), 45.0)
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
        # Deterministic arc-extended projective plane first (gives 394 for d=16).
        cands = _arc_candidates(d, start + 0.2 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c in cands[:1]:
            consider(n_c, E_c)

        # New: difference-cover Haar graphs, searching for m large enough to beat the current order.
        k = d
        mmax = k * (k - 1) + 1
        m0 = best_n // 2 + 1
        if k >= 2 and m0 <= mmax and time.monotonic() < deadline:
            res = _haar_search(k, m0, rng, deadline)
            if res is not None:
                m, S = res
                n, E = lib.haar_graph(m, S)
                consider(n, E)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
