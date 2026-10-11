import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc helpers (D = 3 secondary construction)
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
# D = 3: bi-Cayley graphs over groups of order m.
#
# For a group G of order m and a k-subset S of G, put A = G and B = G with
# a_x ~ b_{x s} for s in S. This is k-regular and bipartite on 2m vertices.
# The diameter is at most 3 iff
#   (i)  S S^{-1} = G   (A-A pairs at distance <= 2, and A-B pairs via S S^{-1} S = G)
#   (ii) S^{-1} S = G   (B-B pairs at distance <= 2)
# Cyclic groups give the Haar graphs of the parent program. Non-cyclic groups
# (direct and semidirect products) offer more covers at the same order, so
# we climb m above the cyclic record and try several groups per order.
# ----------------------------------------------------------------------------

_SLICE_MIN = 0.8
_SLICE_MAX = 4.0


def _group_options(m, rng):
    """Return a list of (mul, inv) for groups of order m: cyclic first, then non-cyclic products."""
    opts = [lib.cyclic_group(m)[1:]]
    for k in range(2, m // 2 + 1):
        if m % k:
            continue
        a = m // k
        if a < 2:
            continue
        rs = [r for r in range(1, a) if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a]
        if not rs:
            continue
        nontriv = [r for r in rs if r != 1]
        picks = [1] + rng.sample(nontriv, min(2, len(nontriv)))
        for r in picks:
            _, mul, inv = lib.semidirect_group(a, k, r)
            opts.append((mul, inv))
    return opts[:6]


def _tables(m, mul, inv):
    """Multiplication table mt[x][y] = x*y and inverse table iv for a group on 0..m-1."""
    mt = [[mul(x, y) for y in range(m)] for x in range(m)]
    iv = [inv(x) for x in range(m)]
    return mt, iv


def _shift(c1, c2, mt, iv, others, x, y):
    """Replace x by y in the set (others + x). Updates coverage counts; returns change in uncovered count."""
    d = 0
    ix = iv[x]
    for o in others:
        io = iv[o]
        for g in (mt[x][io], mt[o][ix]):
            c1[g] -= 1
            if c1[g] == 0:
                d += 1
        for g in (mt[ix][o], mt[io][x]):
            c2[g] -= 1
            if c2[g] == 0:
                d += 1
    iy = iv[y]
    for o in others:
        io = iv[o]
        for g in (mt[y][io], mt[o][iy]):
            if c1[g] == 0:
                d -= 1
            c1[g] += 1
        for g in (mt[iy][o], mt[io][y]):
            if c2[g] == 0:
                d -= 1
            c2[g] += 1
    return d


def _cover_search(k, m, mt, iv, rng, deadline):
    """Find a k-subset S of a group of order m with S S^{-1} = G = S^{-1} S, by annealing. None on timeout."""
    if k > m:
        return None
    if k == m:
        return list(range(m))
    S = rng.sample(range(m), k)
    in_s = set(S)
    c1 = [0] * m
    c2 = [0] * m
    for i in range(k):
        for j in range(k):
            if i != j:
                s, t = S[i], S[j]
                c1[mt[s][iv[t]]] += 1
                c2[mt[iv[s]][t]] += 1
    unc = sum(1 for g in range(1, m) if c1[g] == 0) + sum(1 for g in range(1, m) if c2[g] == 0)
    T = 1.0
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        if it % 200000 == 0:
            T = 0.6  # reheat
        T = max(0.05, T * 0.9999)
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(m)
        if y in in_s:
            continue
        others = S[:i] + S[i + 1:]
        delta = _shift(c1, c2, mt, iv, others, x, y)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            in_s.discard(x)
            in_s.add(y)
            unc += delta
        else:
            _shift(c1, c2, mt, iv, others, y, x)
    return sorted(S)


def _bicayley_graph(m, mt, S):
    """Edges of the bi-Cayley graph: a_x (vertex x) ~ b_{x s} (vertex m + mt[x][s])."""
    return 2 * m, [(x, m + mt[x][s]) for x in range(m) for s in S]


def _haar_stage(k, rng, deadline, consider):
    """Climb the group order m upward from 0.8*mmax; keep feeding every valid success to consider()."""
    mmax = k * (k - 1) + 1
    lo = max(k, int(0.8 * mmax))
    for m in range(lo, mmax + 1):
        found = False
        for mul, inv in _group_options(m, rng):
            now = time.monotonic()
            if now > deadline:
                return
            mt, iv = _tables(m, mul, inv)
            remaining = deadline - now
            slice_ = max(_SLICE_MIN, min(_SLICE_MAX, remaining / 10.0))
            S = _cover_search(k, m, mt, iv, rng, min(deadline, now + slice_))
            if S is not None:
                n, E = _bicayley_graph(m, mt, S)
                consider(n, E)
                found = True
                break
        if not found and time.monotonic() > deadline:
            return


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

    if D == 3 and d >= 2:
        # Primary: bi-Cayley graphs over cyclic and non-cyclic groups of order m.
        _haar_stage(d, rng, start + 0.8 * budget, consider)
        # Secondary: arc-extended projective plane.
        cands = _arc_candidates(d, deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands[:1]:
            consider(n_c, E_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
