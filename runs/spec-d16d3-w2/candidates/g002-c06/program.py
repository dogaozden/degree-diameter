import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), with saturation.
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Each old vertex has degree q+1, so spare capacity is s = d - q - 1. Choose a
# point set S with every line holding <= s points of S and every point lying on
# <= s lines indexed by S. For each P in S add an A-vertex joined to the q+1
# lines through P; for each j in S add a B-vertex joined to the q+1 points on j.
# Then add every missing X-Y edge (X = points + A-vertices, Y = lines + B-vertices)
# while both endpoints have spare degree. This keeps the graph bipartite and can
# only shorten distances.
# ----------------------------------------------------------------------------

def _pg_incidence(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q)."""
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


def _arc_graph(m, edges, point_lines, line_points, S, d, rng):
    """Extended graph plus saturation with spare X-Y edges. Returns (n, sorted edge list)."""
    k = len(S)
    n = 2 * m + 2 * k
    E = set()

    def add(x, y):
        E.add((x, y) if x < y else (y, x))

    for u, v in edges:
        add(u, v)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in point_lines[P]:
            add(a, m + L)
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            add(Q, b)

    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    X = list(range(m)) + list(range(2 * m, 2 * m + k))
    Y = list(range(m, 2 * m)) + list(range(2 * m + k, n))
    spx = [v for v in X if deg[v] < d]
    spy = [v for v in Y if deg[v] < d]
    pairs = [(x, y) for x in spx for y in spy]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d:
            continue
        key = (x, y) if x < y else (y, x)
        if key in E:
            continue
        E.add(key)
        deg[x] += 1
        deg[y] += 1
    return n, sorted(E)


def _arc_for_q(q, d, deadline, rng):
    """Best arc-extended graph for PG(2,q) at max degree d, or None."""
    s = d - q - 1
    if s < 1:
        return None
    m, edges, point_lines, line_points = _pg_incidence(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    cands = [[], _greedy_arc(m, s, point_lines, line_points, rng, 60, deadline)]
    if s >= 2:
        cs = _conic_set(q, index)
        if _loads_ok(cs, s, m, point_lines, line_points):
            cands.append(cs)
    S = max(cands, key=len)
    if not _loads_ok(S, s, m, point_lines, line_points):
        return None
    return _arc_graph(m, edges, point_lines, line_points, S, d, rng)


def _arc_candidates(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        res = _arc_for_q(q, d, deadline, rng)
        if res is not None:
            out.append(res)
    return out


# ----------------------------------------------------------------------------
# Haar graphs from difference covers (diameter 3).
#
# H(m, S) with |S| = d and S - S = Z_m has diameter 3. We search for covers by
# annealing on the number of uncovered differences, and bisect on m.
# ----------------------------------------------------------------------------

def _cover_search(k, m, rng, deadline):
    """Find S subset of Z_m with |S| = k and S - S = Z_m. Returns sorted S, or None."""
    if m < k:
        return None
    if m == k:
        return list(range(m))
    S = rng.sample(range(m), k)
    in_s = set(S)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    T = 1.0
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        if it % 150000 == 0:
            T = 0.5
        T = max(0.05, T * 0.9999)
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(m)
        if y in in_s:
            continue
        others = S[:i] + S[i + 1:]
        delta = 0
        for s in others:
            g = (x - s) % m
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
            g = (s - x) % m
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
        for s in others:
            g = (y - s) % m
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
            g = (s - y) % m
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
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


def _haar_search(k, rng, deadline):
    """Bisect on m for the largest m admitting a difference cover of size k. Returns (m, S)."""
    if k < 2:
        return None
    mmax = k * (k - 1) + 1  # |S - S| <= k(k-1)+1, so m > mmax can never be covered
    lo = k
    best = (k, list(range(k)))  # K_{k,k}, trivially covered
    hi = mmax + 1
    while hi - lo > 1 and time.monotonic() < deadline:
        mid = (lo + hi) // 2
        remaining = deadline - time.monotonic()
        slice_ = max(0.3, remaining / 4.0)
        S = _cover_search(k, mid, rng, min(deadline, time.monotonic() + slice_))
        if S is not None:
            lo = mid
            best = (mid, S)
        else:
            hi = mid
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

    if D >= 3 and d >= 2:
        # Arc-extended projective plane graphs (diameter 3).
        arcs = _arc_candidates(d, start + 0.4 * budget, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, E_c in arcs[:2]:
            consider(n_c, E_c)

        # Haar graph from a difference cover of size d (diameter 3).
        res = _haar_search(d, rng, start + 0.9 * budget)
        if res is not None:
            m, S = res
            n_h, E_h = lib.haar_graph(m, S)
            consider(n_h, E_h)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
