import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction A (D >= 3): arc-extended PG(2, q), as in the parent.
# Points and lines of PG(2,q) plus, for each element of an arc S, one
# A-vertex joined to the lines through it and one B-vertex joined to the
# points on its line. Degrees: point q+1+cp <= d, line q+1+cl <= d.
# ----------------------------------------------------------------------------

def _pg(q):
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


def _conic(q, index):
    F = lib.GF(q)
    keys = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if q % 2 == 0:
        keys.append((0, 1, 0))
    if any(k not in index for k in keys):
        return None
    return [index[k] for k in keys]


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


def _arc_best(d, deadline):
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, pl, lp = _pg(q)
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, random.Random(q * 31 + d), 30, deadline))
        if s >= 2:
            cs = _conic(q, index)
            if cs is not None and _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        n, E = _arc_graph(m, edges, pl, lp, S)
        if best is not None and n <= best[0]:
            continue
        if lib.is_valid(n, E, d, 3):
            best = (n, E)
    return best


# ----------------------------------------------------------------------------
# Construction B (D = 3): bipartite Haar graph H(m, S) with |S| = d.
#
# H(m, S) has parts a_i, b_j and edges a_i b_{i+s}. It is bipartite and
# d-regular, with 2m vertices. Its diameter is at most 3 exactly when
# S - S covers all of Z_m: a-a pairs need a common neighbour (length-2 path),
# and a-b pairs are then reached within 3 steps.
#
# So we search for a d-subset S of Z_m whose difference set covers Z_m,
# with m above the arc record's half-order. The search is simulated annealing
# on the number of uncovered residues, with incremental count updates.
# ----------------------------------------------------------------------------

def _cover_search(m, k, rng, deadline):
    """Return a k-subset S of Z_m with S - S = Z_m, or None if the deadline passes first."""
    if k * (k - 1) < m - 1:
        return None
    S = rng.sample(range(m), k)
    inS = [False] * m
    for x in S:
        inS[x] = True
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for r in range(1, m) if cnt[r] == 0)
    T = 0.4
    step = 0
    while unc > 0:
        step += 1
        if (step & 2047) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(m)
        if inS[y]:
            continue
        others = [S[j] for j in range(k) if j != i]
        ch = 0
        for t in others:
            for r in ((x - t) % m, (t - x) % m):
                cnt[r] -= 1
                if cnt[r] == 0:
                    ch += 1
        for t in others:
            for r in ((y - t) % m, (t - y) % m):
                if cnt[r] == 0:
                    ch -= 1
                cnt[r] += 1
        if ch <= 0 or rng.random() < math.exp(-ch / T):
            S[i] = y
            inS[x] = False
            inS[y] = True
            unc += ch
        else:
            for t in others:
                for r in ((y - t) % m, (t - y) % m):
                    cnt[r] -= 1
            for t in others:
                for r in ((x - t) % m, (t - x) % m):
                    cnt[r] += 1
    return S


def _haar_search(k, lo, hi, rng, deadline):
    """Try m = lo, lo+1, ... ; stop after 4 consecutive failures. Return (m, S) for the largest success."""
    best = None
    fails = 0
    m = lo
    while m <= hi and fails < 4:
        now = time.monotonic()
        if now >= deadline:
            break
        end = min(deadline, now + 8.0)
        S = _cover_search(m, k, rng, end)
        if S is not None:
            best = (m, S)
            fails = 0
        else:
            fails += 1
        m += 1
    return best


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 4.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed * 1000003 + d * 131 + D)

    # Safe fallback: K_{d,d} (Haar graph with S = all residues), diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_E, d, D):
        return 1, []

    if D >= 3:
        # Arc-extended projective plane (the parent's record-level construction).
        arc = _arc_best(d, deadline)
        if arc is not None and arc[0] > best_n and lib.is_valid(arc[0], arc[1], d, D):
            best_n, best_E = arc

        # Difference-cover Haar search: aim above the current order.
        lo = best_n // 2 + 1
        hi = min(d * (d - 1) + 1, lib.moore_bound(d, 3) // 2)
        if lo <= hi and time.monotonic() < deadline:
            found = _haar_search(d, lo, hi, rng, deadline)
            if found is not None:
                m, S = found
                n, E = lib.haar_graph(m, S)
                if n > best_n and lib.is_valid(n, E, d, D):
                    best_n, best_E = n, E

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
