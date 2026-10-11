import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline: arc-extended PG(2,q) incidence graphs (D = 3), as in the parent.
# ----------------------------------------------------------------------------

def _pg_incidence(q):
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
# New construction (D = 3): cyclic Haar graphs from difference covers.
#
# H(Z_m, S) has parts a_i, b_j with a_i ~ b_j iff j - i in S, where |S| = d.
# Two a-vertices are at distance 2 iff their difference lies in S - S, and
# every a-b pair is within distance 3 once S - S = Z_m (since then
# S - S + S = Z_m). So diameter 3 holds exactly when S is a difference cover
# of Z_m. This gives order 2m, with m up to d(d-1)+1 (the Moore bound 2m).
# A simulated-annealing search over d-subsets looks for covers with
# m just above the parent's record half-order.
# ----------------------------------------------------------------------------

def _difference_cover(m, k, rng, end_time, T=0.5):
    """Search a k-subset S of Z_m with S - S = Z_m (nonzero residues). Returns S or None."""
    S = rng.sample(range(m), k)
    inS = [False] * m
    for a in S:
        inS[a] = True
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    zeros = sum(1 for t in range(1, m) if cnt[t] == 0)
    it = 0
    while zeros > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > end_time:
            return None
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(m)
        if inS[y]:
            continue
        others = [S[j] for j in range(k) if j != i]
        old = zeros
        # Remove x.
        for s in others:
            for t in ((x - s) % m, (s - x) % m):
                cnt[t] -= 1
                if cnt[t] == 0:
                    zeros += 1
        # Add y.
        for s in others:
            for t in ((y - s) % m, (s - y) % m):
                if cnt[t] == 0:
                    zeros -= 1
                cnt[t] += 1
        delta = zeros - old
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            inS[x] = False
            inS[y] = True
        else:
            # Undo add y, then undo remove x.
            for s in others:
                for t in ((y - s) % m, (s - y) % m):
                    cnt[t] -= 1
                    if cnt[t] == 0:
                        zeros += 1
            for s in others:
                for t in ((x - s) % m, (s - x) % m):
                    if cnt[t] == 0:
                        zeros -= 1
                    cnt[t] += 1
    return S


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D >= 4), as in the parent.
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, E

    if D >= 3:
        for n_c, E_c in _arc_candidates(d, deadline, random.Random(seed * 7919 + d)):
            consider(n_c, E_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # New bold path for D = 3: cyclic Haar graphs H(Z_m, S) with S a
    # difference cover of size d. Start just above the current record half-order
    # and walk m upward while annealing succeeds.
    if D == 3 and d >= 2:
        m = best_n // 2 + 1
        m_max = d * (d - 1) + 1
        while m <= m_max:
            now = time.monotonic()
            remaining = deadline - now
            if remaining < 1.0:
                break
            S = _difference_cover(m, d, rng, now + 0.5 * remaining)
            if S is None:
                break
            n, E = lib.haar_graph(m, S)
            if not lib.is_valid(n, E, d, D):
                break
            consider(n, E)
            m += 1

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
