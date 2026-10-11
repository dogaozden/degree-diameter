import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Moore bound and projective-plane arc helpers (baseline for D = 3)
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
# D = 3 via Haar graphs over abelian groups.
#
# For a group G of order m and S subset of G with |S| = k, the Haar graph has
# parts A = G, B = G and a_g ~ b_{g+s} for s in S. It is k-regular and bipartite.
# It has diameter 3 exactly when S - S = G (a "difference cover").
#
# The parent only searched cyclic groups Z_m. Here we also search the
# non-cyclic groups Z_n1 x Z_n2 (n1 | n2) of each order m, which can admit
# covers where cyclic ones fail. We climb m upward from just above the
# current baseline, so each success is a strict improvement.
# ----------------------------------------------------------------------------

def _group_types(m):
    """Return (n1, n2) with n1 | n2 and n1*n2 = m, cyclic (1, m) first."""
    out = []
    for n1 in range(1, math.isqrt(m) + 1):
        if m % n1 == 0:
            n2 = m // n1
            if n2 % n1 == 0:
                out.append((n1, n2))
    out.sort(key=lambda t: t[0])
    return out


def _group_tables(n1, n2):
    """Addition table A and difference table D (D[a][b] = a - b) for Z_n1 x Z_n2, element x*n2 + y."""
    m = n1 * n2

    def add(a, b):
        x1, y1 = divmod(a, n2)
        x2, y2 = divmod(b, n2)
        return ((x1 + x2) % n1) * n2 + (y1 + y2) % n2

    def neg(a):
        x, y = divmod(a, n2)
        return ((-x) % n1) * n2 + (-y) % n2

    A = [[add(a, b) for b in range(m)] for a in range(m)]
    ng = [neg(b) for b in range(m)]
    D = [[A[a][ng[b]] for b in range(m)] for a in range(m)]
    return A, D


def _cover(k, m, D, rng, deadline):
    """Find S in G (|G| = m, given difference table D) with |S| = k and S - S = G, or None."""
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
                cnt[D[a][b]] += 1
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
        # Remove x's differences.
        for s in others:
            g = D[x][s]
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
            g = D[s][x]
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
        # Add y's differences.
        for s in others:
            g = D[y][s]
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
            g = D[s][y]
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
                cnt[D[y][s]] -= 1
                cnt[D[s][y]] -= 1
            for s in others:
                cnt[D[x][s]] += 1
                cnt[D[s][x]] += 1
    return sorted(S)


def _haar_group_search(k, lo, rng, deadline):
    """Climb m upward from lo over all abelian group types; return (m, A, S) for the largest success."""
    mmax = k * (k - 1) + 1
    best = None
    m = lo
    while m <= mmax and time.monotonic() < deadline:
        found = False
        for n1, n2 in _group_types(m):
            now = time.monotonic()
            if now >= deadline:
                break
            slice_ = min(max(0.5, (deadline - now) / 3.0), 6.0)
            A, D = _group_tables(n1, n2)
            S = _cover(k, m, D, rng, min(deadline, now + slice_))
            if S is not None:
                best = (m, A, S)
                found = True
                break
        if not found:
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
    budget = min(0.75 * float(time_limit), 42.0)
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
        # Baseline: arc-extended projective plane (quick).
        cands = _arc_candidates(d, start + 0.15 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c in cands[:1]:
            consider(n_c, E_c)

        # Main: Haar graph over an abelian group with a difference cover of size d.
        # Start just above the current baseline so any success is a strict improvement.
        if d >= 2:
            lo = max(d, best_n // 2 + 1)
            res = _haar_group_search(d, lo, rng, start + 0.92 * budget)
            if res is not None:
                m, A, S = res
                E = [(g, m + A[g][s]) for g in range(m) for s in S]
                consider(2 * m, E)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
