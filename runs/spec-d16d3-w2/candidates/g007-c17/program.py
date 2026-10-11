import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# PG(2,q) incidence data and arc-extended graphs (D = 3).
#
# Points and lines of PG(2,q) are both indexed by the same normalized vectors.
# Add an A-vertex per point P in S_A, joined to the lines through P, and a
# B-vertex per line j in S_B, joined to the points on j. Each line then gains
# load |{P in S_A : P on L}| and each point gains |{j in S_B : Q on j}|. Both
# loads must stay within the spare degree s = d - (q+1). Any such pair of sets
# gives diameter 3, so only degrees matter. With s = 2, S_A and S_B must be
# arcs, which caps each at q+1 (or q+2 for even q).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, points) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        L = v - m
        point_lines[u].append(L)
        line_points[L].append(u)
    return m, edges, point_lines, line_points, lib.projective_points(q)


def _conic(q, index):
    """Conic (plus nucleus for even q): a (q+1)- or (q+2)-arc, so every line has at most 2 of its points."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _pg_arc_graph(data, SA, SB):
    """Incidence graph of PG(2,q) plus A-vertices for SA and B-vertices for SB."""
    m, edges, point_lines, line_points = data[:4]
    k1, k2 = len(SA), len(SB)
    n = 2 * m + k1 + k2
    E = list(edges)
    for t, P in enumerate(SA):
        a = 2 * m + t
        for L in point_lines[P]:
            E.append((a, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + k1 + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


# ----------------------------------------------------------------------------
# New routine: tabu search for cyclic difference covers, giving Haar graphs.
#
# H(m, S) with |S| = d and S - S = Z_m has diameter 3 and order 2m. The record
# arc construction gives 394 = 2*197 at d = 16, so a cover with m >= 198 beats it.
# The search swaps one element of S per step. Each step is chosen as the best of
# a random sample of candidate swaps under the uncovered-difference count, with a
# short tabu tenure and perturbation on stagnation.
# ----------------------------------------------------------------------------

_CAND = 40


def _swap(S, i, y, cnt, m, commit):
    """Replace S[i] by y, updating cnt over ordered differences. Return the change in uncovered count.

    If commit is False, the change is reverted before returning.
    """
    x = S[i]
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
    if not commit:
        for s in others:
            cnt[(y - s) % m] -= 1
            cnt[(s - y) % m] -= 1
        for s in others:
            cnt[(x - s) % m] += 1
            cnt[(s - x) % m] += 1
    return delta


def _tabu_cover(k, m, rng, deadline):
    """Find S subset of Z_m with |S| = k and S - S = Z_m, or return None at the deadline."""
    if m <= k:
        return None
    S = rng.sample(range(m), k)
    in_s = [False] * m
    for x in S:
        in_s[x] = True
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    tabu_until = [0] * m
    best_unc = unc
    stall = 0
    it = 0
    while unc > 0:
        it += 1
        if it % 16 == 0 and time.monotonic() > deadline:
            return None
        bd = None
        bi = bj = -1
        for _ in range(_CAND):
            i = rng.randrange(k)
            y = rng.randrange(m)
            if in_s[y] or tabu_until[y] > it:
                continue
            delta = _swap(S, i, y, cnt, m, False)
            if bd is None or delta < bd or (delta == bd and rng.random() < 0.3):
                bd, bi, bj = delta, i, y
        if bd is None:
            continue
        x = S[bi]
        unc += _swap(S, bi, bj, cnt, m, True)
        in_s[x] = False
        in_s[bj] = True
        S[bi] = bj
        tabu_until[x] = it + 2 + rng.randrange(7)
        if unc < best_unc:
            best_unc = unc
            stall = 0
        else:
            stall += 1
            if stall > 1500:
                for _ in range(2):
                    i = rng.randrange(k)
                    y = rng.randrange(m)
                    while in_s[y]:
                        y = rng.randrange(m)
                    x = S[i]
                    unc += _swap(S, i, y, cnt, m, True)
                    in_s[x] = False
                    in_s[y] = True
                    S[i] = y
                stall = 0
                best_unc = unc
    return sorted(S)


def _haar_grow(k, m0, rng, deadline):
    """Try m = m0, m0+1, ... while covers are found before the deadline. Return (m, S) or None."""
    mmax = k * (k - 1) + 1
    best = None
    m = m0
    while m <= mmax and time.monotonic() < deadline:
        S = _tabu_cover(k, m, rng, deadline)
        if S is None:
            break
        best = (m, S)
        m += 1
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4), kept from the parent.
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
    budget = min(0.7 * float(time_limit), 40.0)
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
        # Arc-extended PG(2,q): q + 1 + s = d, with s spare degree per vertex.
        for q in range(2, d):
            if not lib.is_prime_power(q):
                continue
            s = d - q - 1
            if s < 0:
                continue
            data = _pg_data(q)
            if s >= 2:
                index = {p: i for i, p in enumerate(data[4])}
                S = _conic(q, index)
                n, E = _pg_arc_graph(data, S, S)
            else:
                n, E = _pg_arc_graph(data, [], [])
            consider(n, E)

        # New: tabu search for a difference cover of size d, giving Haar graphs of order 2m.
        k = d
        m0 = best_n // 2 + 1
        mmax = k * (k - 1) + 1
        if k >= 2 and m0 <= mmax and time.monotonic() < deadline:
            res = _haar_grow(k, m0, rng, deadline)
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
