import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Common helpers
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


# ----------------------------------------------------------------------------
# Arc-extended projective plane (parent construction, kept as a fallback).
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
# NEW construction for D = 3: cyclic bi-Cayley (Haar) graphs.
#
# Vertices a_i, b_j for i, j in Z_m; a_i ~ b_{i+s} for s in S, |S| = d.
# Degree is d. Same-side distance 2 holds iff S - S covers Z_m. Cross-side
# distance <= 3 then holds automatically, since for any x, x - s lies in
# S - S for any fixed s in S. So the only requirement is S - S = Z_m, and
# m <= d^2 - d + 1. This gives n = 2m, reaching the Moore-type ceiling
# 2(d^2 - d + 1) when a perfect difference set exists.
# ----------------------------------------------------------------------------

def _cover_search(m, k, rng, deadline):
    """Simulated annealing for S (|S| = k, 0 in S) with S - S covering Z_m. Returns sorted S or None."""
    if k < 2 or k > m:
        return None
    S = [0] + rng.sample(range(1, m), k - 1)
    inS = set(S)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = 0
    for x in range(1, m):
        if cnt[x] == 0:
            unc += 1
    T = 0.4
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        idx = rng.randrange(1, k)
        s = S[idx]
        r = rng.randrange(m)
        if r in inS:
            continue
        others = [t for t in S if t != s]
        new_unc = unc
        for t in others:
            x = (s - t) % m
            cnt[x] -= 1
            if cnt[x] == 0:
                new_unc += 1
            y = (t - s) % m
            cnt[y] -= 1
            if cnt[y] == 0:
                new_unc += 1
        for t in others:
            x = (r - t) % m
            if cnt[x] == 0:
                new_unc -= 1
            cnt[x] += 1
            y = (t - r) % m
            if cnt[y] == 0:
                new_unc -= 1
            cnt[y] += 1
        if new_unc <= unc or rng.random() < math.exp(-(new_unc - unc) / T):
            S[idx] = r
            inS.discard(s)
            inS.add(r)
            unc = new_unc
        else:
            for t in others:
                cnt[(r - t) % m] -= 1
                cnt[(t - r) % m] -= 1
            for t in others:
                cnt[(s - t) % m] += 1
                cnt[(t - s) % m] += 1
    return sorted(S)


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4), unchanged from parent.
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
    deadline = start + 0.7 * time_limit
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

    if D == 2:
        return best_n, list(best_E)

    if D == 3:
        # Arc-extended PG(2,q) graphs (parent construction, fallback).
        arc_deadline = start + 0.2 * time_limit
        for n_c, E_c in _arc_candidates(d, arc_deadline, random.Random(seed * 7919 + d)):
            consider(n_c, E_c)

        # Bold change: binary search on m for a cyclic Haar graph with S - S = Z_m.
        lo, hi = max(d, 2), d * d - d + 1
        while lo <= hi:
            now = time.monotonic()
            remaining = deadline - now
            if remaining < 0.2:
                break
            mid = (lo + hi) // 2
            S = _cover_search(mid, d, rng, now + min(6.0, remaining))
            if S is not None:
                n_h, E_h = lib.haar_graph(mid, S)
                consider(n_h, E_h)
                lo = mid + 1
            else:
                hi = mid - 1

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
