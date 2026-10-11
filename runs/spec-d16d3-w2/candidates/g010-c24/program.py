import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc-extended incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d-q-1. For a point set S whose
# line-loads and point-loads are at most s, add an A-vertex per point of S
# (joined to the q+1 lines through it) and a B-vertex per point of S (joined to
# the q+1 points on that line). Order 2(q^2+q+1) + 2|S|.
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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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
    """For each prime power q with q+1 <= d, build the arc-extended PG(2,q) graph."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points = _pg_incidence(q)
        index = {p: i for i, p in enumerate(lib.projective_points(q))}
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
# Haar graphs from difference covers (diameter 3).
#
# H(m, S): a_i ~ b_{i+s} for s in S, |S| = k, so it is k-regular bipartite on
# 2m vertices. Diameter <= 3 iff S - S = Z_m (then S + (S - S) = Z_m covers
# mixed pairs). We search S by targeted annealing: pick an uncovered difference
# g and move one element to base + g for some other element base.
# ----------------------------------------------------------------------------

def _cover(k, m, rng, deadline):
    """Find S subset of Z_m, |S| = k, with S - S = Z_m. Returns sorted S, or None on timeout."""
    if m < k or k < 2:
        return None
    S = rng.sample(range(m), k)
    inS = [False] * m
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    T = 0.45
    it = 0
    while unc > 0:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            return None
        ug = [g for g in range(1, m) if cnt[g] == 0]
        g = rng.choice(ug)
        j = rng.randrange(k)
        if rng.random() < 0.12:
            y = rng.randrange(m)
            i = rng.randrange(k)
        else:
            y = (S[j] + g) % m
            i = rng.randrange(k - 1)
            if i >= j:
                i += 1
        if inS[y]:
            continue
        x = S[i]
        others = S[:i] + S[i + 1:]
        before = unc
        for s in others:
            for dd in ((x - s) % m, (s - x) % m):
                cnt[dd] -= 1
                if cnt[dd] == 0:
                    unc += 1
        for s in others:
            for dd in ((y - s) % m, (s - y) % m):
                if cnt[dd] == 0:
                    unc -= 1
                cnt[dd] += 1
        delta = unc - before
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            inS[x] = False
            inS[y] = True
        else:
            for s in others:
                for dd in ((y - s) % m, (s - y) % m):
                    cnt[dd] -= 1
                    if cnt[dd] == 0:
                        unc += 1
            for s in others:
                for dd in ((x - s) % m, (s - x) % m):
                    if cnt[dd] == 0:
                        unc -= 1
                    cnt[dd] += 1
    return sorted(S)


def _haar_climb(k, m_lo, deadline, rng, consider):
    """Search covers for m = m_lo, m_lo+1, ...; each success is offered to consider()."""
    mmax = k * (k - 1) + 1
    m = max(k, m_lo)
    best = None
    while m <= mmax and time.monotonic() < deadline:
        S = _cover(k, m, rng, deadline)
        if S is None:
            break
        best = (m, S)
        consider(*lib.haar_graph(m, S))
        m += 1
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used only when D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    budget = max(1.0, min(0.8 * float(time_limit), float(time_limit) - 10.0))
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
        # Arc-extended projective plane graph (the record family for d=16).
        arcs = _arc_candidates(d, start + 0.15 * budget, random.Random(seed * 7919 + d))
        if arcs:
            arcs.sort(key=lambda t: -t[0])
            consider(arcs[0][0], arcs[0][1])

        # Haar graphs from difference covers: order 2m beats best_n iff m > best_n // 2.
        k = d
        m_lo = best_n // 2 + 1
        mmax = k * (k - 1) + 1
        if m_lo <= mmax and time.monotonic() < deadline:
            _haar_climb(k, m_lo, deadline, rng, consider)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
