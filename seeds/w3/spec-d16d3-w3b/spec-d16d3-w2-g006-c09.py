import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Group tables for abelian groups Z_a x Z_b (a | b).  Element x = i*b + j.
# Z_m (a = 1) is the cyclic case.  Non-cyclic groups are the new ingredient:
# a difference cover S - S = G in a non-cyclic abelian group G gives a Haar-type
# bipartite graph of order 2|G| and diameter 3, via lib.group_lift.
# ----------------------------------------------------------------------------

_TCACHE = {}


def _tables(a, b):
    """Subtraction and addition tables for G = Z_a x Z_b, element i*b + j."""
    key = (a, b)
    if key in _TCACHE:
        return _TCACHE[key]
    m = a * b
    SUB = [[0] * m for _ in range(m)]
    ADD = [[0] * m for _ in range(m)]
    for x in range(m):
        xi, xj = divmod(x, b)
        Sx, Ax = SUB[x], ADD[x]
        for y in range(m):
            yi, yj = divmod(y, b)
            Sx[y] = ((xi - yi) % a) * b + (xj - yj) % b
            Ax[y] = ((xi + yi) % a) * b + (xj + yj) % b
    _TCACHE[key] = (SUB, ADD)
    return SUB, ADD


def _abelian_groups(m):
    """All (a, b) with a*b = m and a | b; (1, m) is the cyclic group, listed first."""
    out = []
    for a in range(1, math.isqrt(m) + 1):
        if m % a == 0:
            b = m // a
            if b % a == 0:
                out.append((a, b))
    return out


def _anneal(k, m, SUB, rng, deadline):
    """Find S in G (|G| = m, S[0] = 0 WLOG) with |S| = k and S - S = G, or None on timeout."""
    S = [0] + rng.sample(range(1, m), k - 1)
    in_s = set(S)
    cnt = [0] * m
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[SUB[S[i]][S[j]]] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    T = 0.6
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        if it % 200000 == 0:
            T = 0.6
        T = max(0.08, T * 0.99995)
        i = rng.randrange(1, k)
        x = S[i]
        y = rng.randrange(m)
        if y in in_s:
            continue
        others = S[:i] + S[i + 1:]
        delta = 0
        # Remove the differences involving x.
        for s in others:
            g = SUB[x][s]
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
            g = SUB[s][x]
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
        # Add the differences involving y.
        for s in others:
            g = SUB[y][s]
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
            g = SUB[s][y]
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
                cnt[SUB[y][s]] -= 1
                cnt[SUB[s][y]] -= 1
            for s in others:
                cnt[SUB[x][s]] += 1
                cnt[SUB[s][x]] += 1
    return sorted(S)


def _search_cover(k, a, b, rng, deadline):
    """Difference cover of size k in Z_a x Z_b, or None."""
    m = a * b
    if m < k:
        return None
    if m == k:
        return list(range(m))
    SUB, _ = _tables(a, b)
    return _anneal(k, m, SUB, rng, deadline)


def _haar_search(k, rng, deadline):
    """Climb the group order m upward over all abelian groups; return (m, a, b, S) for the largest success."""
    if k < 3:
        return None
    mmax = k * (k - 1) + 1
    m = max(k + 1, int(0.75 * mmax))
    best = None
    fails = 0
    while m <= mmax and time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        groups = _abelian_groups(m)
        per_m = max(0.5, min(remaining / 3.0, 8.0))
        per_g = max(0.2, per_m / max(1, len(groups)))
        found = None
        for a, b in groups:
            if time.monotonic() >= deadline:
                break
            S = _search_cover(k, a, b, rng, min(deadline, time.monotonic() + per_g))
            if S is not None:
                found = (m, a, b, S)
                break
        if found is not None:
            best = found
            fails = 0
        else:
            fails += 1
            if fails >= 3:
                break
        m += 1
    return best


# ----------------------------------------------------------------------------
# Projective-plane arc extension (D = 3 secondary candidate)
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
# Generalized quadrangle W(q) (D = 4 baseline)
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

    if D == 3 and d >= 3:
        # Primary: bipartite Haar graph over an abelian group G with a difference cover S (S - S = G).
        res = _haar_search(d, rng, start + 0.7 * budget)
        if res is not None:
            m, a, b, S = res
            _, ADD = _tables(a, b)
            n, E = lib.group_lift(2, [(0, 1, s) for s in S], m, lambda x, y: ADD[x][y])
            consider(n, E)
        # Secondary: arc-extended projective plane.
        cands = _arc_candidates(d, start + 0.9 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c in cands[:1]:
            consider(n_c, E_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
