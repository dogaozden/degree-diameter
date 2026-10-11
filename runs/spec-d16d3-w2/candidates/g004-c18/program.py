import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended PG(2,q) baseline (diameter 3). Kept as a strong fallback.
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
# New construction: cyclic Haar graphs from difference coverings.
#
# H(Z_m, S) with |S| = d has parts A = Z_m, B = Z_m and a_i ~ b_{i+s}.
# It is d-regular and bipartite on 2m vertices. It has diameter <= 3 exactly
# when S - S = Z_m: same-side pairs are at distance 2 (difference in S - S),
# and cross pairs are at distance 1 or 3 (difference in S - S + S = Z_m).
# Since |S - S| <= d(d-1)+1, this gives n <= 2(d^2-d+1), the Moore bound.
# Finding S is a local search that minimizes the number of uncovered residues.
# ----------------------------------------------------------------------------

def _bump(cnt, r, dl, unc):
    """Change cnt[r] by dl, keeping unc[0] = number of residues in 1..m-1 with cnt == 0."""
    b = cnt[r]
    a = b + dl
    cnt[r] = a
    if b == 0 and a > 0:
        unc[0] -= 1
    elif b > 0 and a == 0:
        unc[0] += 1


def _try_cover(m, k, deadline, rng):
    """Find a k-subset S of Z_m with S - S = Z_m by annealing; return sorted S or None."""
    if k < 1 or k > m or k * (k - 1) + 1 < m:
        return None
    S = rng.sample(range(m), k)
    inS = set(S)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = [sum(1 for r in range(1, m) if cnt[r] == 0)]
    it = 0
    T = 0.4
    while unc[0] > 0:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(k)
        a = S[i]
        x = rng.randrange(m)
        if x in inS:
            continue
        others = S[:i] + S[i + 1:]
        old = unc[0]
        for b in others:
            _bump(cnt, (a - b) % m, -1, unc)
            _bump(cnt, (b - a) % m, -1, unc)
        for b in others:
            _bump(cnt, (x - b) % m, 1, unc)
            _bump(cnt, (b - x) % m, 1, unc)
        delta = unc[0] - old
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            inS.discard(a)
            inS.add(x)
        else:
            for b in others:
                _bump(cnt, (x - b) % m, -1, unc)
                _bump(cnt, (b - x) % m, -1, unc)
            for b in others:
                _bump(cnt, (a - b) % m, 1, unc)
                _bump(cnt, (b - a) % m, 1, unc)
    return sorted(S)


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

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

    # Arc-extended PG(2,q) baseline for D >= 3.
    if D >= 3:
        cands = _arc_candidates(d, start + 0.15 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c in cands[:3]:
            consider(n_c, E_c)

    # New construction for D = 3: cyclic Haar graphs H(Z_m, S), |S| = d, S - S = Z_m.
    if D == 3 and d >= 2:
        rng = random.Random(seed * 104729 + d * 31 + 7)
        m_max = d * (d - 1) + 1
        m = max(best_n // 2 + 1, d)
        while m <= m_max and time.monotonic() < deadline:
            now = time.monotonic()
            remaining = deadline - now
            budget = max(3.0, remaining * 0.4)
            sub_deadline = min(deadline, now + budget)
            S = _try_cover(m, d, sub_deadline, rng)
            if S is None:
                break
            n_h, E_h = lib.haar_graph(m, S)
            consider(n_h, E_h)
            m += 1

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
