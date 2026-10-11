import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy
#
# For D = 3 the new main construction is a cyclic Haar graph H(Z_m, S) with
# |S| = d. Vertices a_i and b_j are joined when j - i is in S. The graph is
# d-regular and bipartite. Same-side pairs are at distance <= 2 exactly when
# S - S covers Z_m, and cross pairs are then at distance <= 3 automatically,
# since S - S + S = Z_m. So we search for a d-subset S with S - S = Z_m and m
# as large as possible. The order is 2m, and the ceiling is m <= d(d-1)+1.
#
# The search is simulated annealing on the number of uncovered nonzero
# differences, with O(d) incremental updates per move.
#
# Fallbacks (always kept): K_{d,d}, the PG(2,q)+arc construction (the parent's
# 394 record for d=16), and the W(q) generalized quadrangle for D >= 4.
# Every candidate is checked with lib.is_valid before it is kept.
# ----------------------------------------------------------------------------


# ----------------------------------------------------------------------------
# Projective-plane arc fallback (from parent)
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


def _arc_best(d, deadline, rng):
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
        s = d - q - 1
        if s < 0:
            continue
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
        n, E = _arc_graph(m, edges, point_lines, line_points, S)
        if lib.is_valid(n, E, d, 3) and (best is None or n > best[0]):
            best = (n, E)
    return best


# ----------------------------------------------------------------------------
# Cyclic difference-cover search for Haar graphs (new main construction, D = 3)
# ----------------------------------------------------------------------------

def _move(S, cnt, m, d, i, new):
    """Replace S[i] by new, updating difference counts. Returns the change in the number of uncovered nonzero residues."""
    old = S[i]
    ch = 0
    for j in range(d):
        if j != i:
            a = S[j]
            for x in ((old - a) % m, (a - old) % m):
                cnt[x] -= 1
                if cnt[x] == 0:
                    ch += 1
    for j in range(d):
        if j != i:
            a = S[j]
            for x in ((new - a) % m, (a - new) % m):
                if cnt[x] == 0:
                    ch -= 1
                cnt[x] += 1
    S[i] = new
    return ch


def _haar_search(m, d, rng, deadline):
    """Find S subset of Z_m, |S| = d, with S - S = Z_m. Returns S or None on timeout."""
    S = rng.sample(range(m), d)
    cnt = [0] * m
    for i in range(d):
        for j in range(d):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)
    inS = set(S)
    T = 0.35
    it = 0
    while unc:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        old = S[i]
        v = rng.randrange(m)
        if v in inS:
            continue
        delta = _move(S, cnt, m, d, i, v)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            inS.discard(old)
            inS.add(v)
            unc += delta
        else:
            _move(S, cnt, m, d, i, old)
    return S


def _haar_ascend(d, deadline, rng, consider):
    """Try m = d+1, d+2, ... up to the difference-cover ceiling; stop at the first failure."""
    m_max = d * (d - 1) + 1
    for m in range(d + 1, m_max + 1):
        now = time.monotonic()
        if now >= deadline:
            break
        attempt_end = now + max(0.5, 0.4 * (deadline - now))
        S = _haar_search(m, d, rng, min(attempt_end, deadline))
        if S is None:
            break
        n, E = lib.haar_graph(m, S)
        consider(n, E)


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q), D = 4 (from parent)
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
    t0 = time.monotonic()
    end = t0 + 0.8 * time_limit
    rng = random.Random(seed * 7919 + d * 131 + D)

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

    if D == 3 and d >= 2:
        # Parent's arc construction first: it is a fast, strong fallback (394 for d=16).
        arc = _arc_best(d, t0 + 0.25 * (end - t0), random.Random(seed * 104729 + d))
        if arc is not None:
            consider(arc[0], arc[1])
        # New main construction: cyclic Haar graphs from difference covers.
        _haar_ascend(d, end, rng, consider)

    if D >= 4 and d >= 3 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
