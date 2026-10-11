import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Moore bound and projective-plane arc helpers (D = 3 secondary construction)
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


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
# D = 3 primary construction: group Haar graphs with tabu-searched covers.
#
# For a finite group G of order m and a k-subset S of G, the Haar graph has
# parts A = G, B = G and edges a_x -- b_{x s} for s in S. It is k-regular and
# bipartite, with 2m vertices. A-A distances are <= 2 iff S S^{-1} = G, and
# B-B distances are <= 2 iff S^{-1} S = G. Mixed pairs are then within 3.
# For nonabelian G the two conditions differ, so both are tracked.
#
# New here: a min-conflicts tabu search. Each step picks an uncovered
# difference g and a member t of S, then proposes new elements y that would
# realize g in one of the four ordered pair forms. Only the best
# (position, y) move among a sample is applied. Non-cyclic groups
# (semidirect products Z_m x| Z_k) are tried alongside the cyclic group.
# ----------------------------------------------------------------------------

def _group_tables(order, mul, inv):
    """Multiplication table M[a][b] and inverse list I[a] for a finite group with elements 0..order-1."""
    M = [[mul(a, b) for b in range(order)] for a in range(order)]
    I = [inv(a) for a in range(order)]
    return M, I


def _groups_of_order(m, rng):
    """Cyclic group of order m first, then one random semidirect Z_mm x| Z_kk per factorization m = mm*kk."""
    out = [lib.cyclic_group(m)]
    for kk in range(2, m):
        if m % kk:
            continue
        mm = m // kk
        if mm < 2:
            continue
        rs = [r for r in range(2, mm) if math.gcd(r, mm) == 1 and pow(r, kk, mm) == 1 % mm]
        if rs:
            out.append(lib.semidirect_group(mm, kk, rng.choice(rs)))
    return out


def _swap(S, i, y, c1, c2, M, I):
    """Replace S[i] by y, updating the two difference counters. Returns change in deficit."""
    x = S[i]
    Ix = I[x]
    others = S[:i] + S[i + 1:]
    delta = 0
    for s in others:
        Is = I[s]
        g = M[x][Is]; c1[g] -= 1; delta += (c1[g] == 0)
        g = M[Ix][s]; c2[g] -= 1; delta += (c2[g] == 0)
        g = M[s][Ix]; c1[g] -= 1; delta += (c1[g] == 0)
        g = M[Is][x]; c2[g] -= 1; delta += (c2[g] == 0)
    Iy = I[y]
    for s in others:
        Is = I[s]
        g = M[y][Is]; delta -= (c1[g] == 0); c1[g] += 1
        g = M[Iy][s]; delta -= (c2[g] == 0); c2[g] += 1
        g = M[s][Iy]; delta -= (c1[g] == 0); c1[g] += 1
        g = M[Is][y]; delta -= (c2[g] == 0); c2[g] += 1
    S[i] = y
    return delta


def _tabu_cover(k, order, M, I, rng, deadline):
    """Find a k-subset S of the group with S S^{-1} = G = S^{-1} S (identity excluded). Returns list or None."""
    if order < k or order - 1 > k * (k - 1):
        return None
    S = rng.sample(range(order), k)
    c1 = [0] * order
    c2 = [0] * order
    for a in S:
        for b in S:
            if a != b:
                c1[M[a][I[b]]] += 1
                c2[M[I[a]][b]] += 1
    deficit = sum((c1[g] == 0) + (c2[g] == 0) for g in range(1, order))
    inS = set(S)
    tabu = {}
    it = 0
    while deficit > 0:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            return None
        unc = [g for g in range(1, order) if c1[g] == 0 or c2[g] == 0]
        g = rng.choice(unc)
        t = S[rng.randrange(k)]
        Ig = I[g]
        cands = (M[g][t], M[Ig][t], M[t][Ig], M[t][g])
        cands = [y for y in cands if y not in inS and tabu.get(y, 0) < it]
        if not cands:
            continue
        y = rng.choice(cands)
        idxs = range(k) if k <= 8 else rng.sample(range(k), 8)
        best_i, best_d = None, None
        for i in idxs:
            x = S[i]
            d_move = _swap(S, i, y, c1, c2, M, I)
            _swap(S, i, x, c1, c2, M, I)
            if best_d is None or d_move < best_d or (d_move == best_d and rng.random() < 0.5):
                best_i, best_d = i, d_move
        x = S[best_i]
        _swap(S, best_i, y, c1, c2, M, I)
        inS.discard(x)
        inS.add(y)
        deficit += best_d
        tabu[x] = it + 5 + rng.randrange(8)
    return sorted(S)


def _find_cover(k, m, rng, deadline):
    """Try each group of order m in turn, sharing the remaining time. Returns (order, mul, S) or None."""
    groups = _groups_of_order(m, rng)
    for idx, (order, mul, inv) in enumerate(groups):
        now = time.monotonic()
        if now >= deadline:
            break
        slot_end = now + (deadline - now) / (len(groups) - idx)
        M, I = _group_tables(order, mul, inv)
        S = _tabu_cover(k, order, M, I, rng, min(deadline, slot_end))
        if S is not None:
            return order, mul, S
    return None


def _haar_search(k, rng, deadline):
    """Climb m upward from a fairly high start; keep the largest m with a valid group cover. Returns (m, order, mul, S) or None."""
    if k < 2:
        return None
    mmax = k * (k - 1) + 1
    m = max(k, int(0.7 * mmax))
    best = None
    fails = 0
    while m <= mmax and time.monotonic() < deadline:
        now = time.monotonic()
        rem = deadline - now
        slice_end = now + max(0.5, rem / 3.0)
        res = _find_cover(k, m, rng, min(deadline, slice_end))
        if res is not None:
            order, mul, S = res
            best = (m, order, mul, S)
            fails = 0
        else:
            fails += 1
            if fails >= 2:
                break
        m += 1
    return best


def _group_haar(order, mul, S):
    """Haar graph over a group: a_x = x, b_y = order + y, edges a_x -- b_{x*s} for s in S."""
    E = []
    for x in range(order):
        for s in S:
            E.append((x, order + mul(x, s)))
    return 2 * order, E


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
        # Primary: group Haar graph from a tabu-searched difference cover of size d.
        if d >= 2:
            res = _haar_search(d, rng, start + 0.65 * budget)
            if res is not None:
                m, order, mul, S = res
                n, E = _group_haar(order, mul, S)
                consider(n, E)
        # Secondary: arc-extended projective plane (the parent construction).
        cands = _arc_candidates(d, start + 0.9 * budget, random.Random(seed * 7919 + d))
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
