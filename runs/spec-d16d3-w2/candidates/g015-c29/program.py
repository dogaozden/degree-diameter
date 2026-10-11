import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc helpers (baseline for D = 3, the parent's construction)
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
# Bold change for D = 3: bi-Cayley graphs over (possibly non-abelian) groups.
#
# Graph: parts A = G and B = G, with a_x ~ b_{x s} for s in S, |S| = d.
# Distance <= 2 for A-A pairs needs S S^{-1} = G; for B-B pairs it needs
# S^{-1} S = G. If S S^{-1} = G then S S^{-1} S = G as well, which covers the
# mixed A-B pairs at distance 3. So diameter 3 holds iff both covers hold.
# Groups: Z_N and semidirect products Z_m x|_r Z_k (r = 1 gives abelian).
# We anneal S to make both covers hold, for orders N with 2N above the
# current best. Any result is validated with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _cover_cost(S, M, I, N):
    """Number of group elements missing from S S^{-1} plus those missing from S^{-1} S."""
    Si = [I[s] for s in S]
    a = set()
    b = set()
    for s in S:
        row = M[s]
        for u in Si:
            a.add(row[u])      # s * t^{-1}
    for u in Si:
        row = M[u]
        for t in S:
            b.add(row[t])      # s^{-1} * t
    return 2 * N - len(a) - len(b)


def _anneal(k, N, M, I, rng, deadline):
    """Find S of size k in G with both covers. Returns sorted S or None."""
    if k > N:
        return None
    S = rng.sample(range(N), k)
    cost = _cover_cost(S, M, I, N)
    T = 2.0
    it = 0
    while cost > 0:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(k)
        y = rng.randrange(N)
        if y in S:
            continue
        old = S[i]
        S[i] = y
        c2 = _cover_cost(S, M, I, N)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            S[i] = old
        T = max(0.1, T * 0.999)
    return sorted(S)


def _groups_of_order(N, rng):
    """Return a list of (mul, inv) for cyclic and small semidirect groups of order N."""
    groups = [lib.cyclic_group(N)[1:]]
    for k in range(2, 7):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        rng.shuffle(rs)
        for r in rs[:3]:
            _, mul, inv = lib.semidirect_group(m, k, r)
            groups.append((mul, inv))
    return groups


def _group_search(k, N, rng, deadline, slice_s):
    """Try each group of order N; return (S, mul) on success, else None."""
    for mul, inv in _groups_of_order(N, rng):
        now = time.monotonic()
        if now > deadline:
            break
        M = [[mul(x, y) for y in range(N)] for x in range(N)]
        I = [inv(x) for x in range(N)]
        S = _anneal(k, N, M, I, rng, min(deadline, now + slice_s))
        if S is not None:
            return S, mul
    return None


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4)
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
    budget = min(0.75 * float(time_limit), 45.0)
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
        # Baseline: arc-extended projective plane (the parent's construction).
        arc_deadline = start + 0.3 * budget
        cands = _arc_candidates(d, arc_deadline, random.Random(seed * 7919 + d))
        if cands:
            n_c, E_c = max(cands, key=lambda t: t[0])
            consider(n_c, E_c)

        # Bold search: bi-Cayley graphs over non-abelian groups.
        # Only orders N with 2N > best_n can improve, and N <= k(k-1)+1.
        k = d
        lo = best_n // 2 + 1
        hi = k * (k - 1) + 1
        for N in range(lo, hi + 1):
            if time.monotonic() > deadline:
                break
            res = _group_search(k, N, rng, deadline, slice_s=0.7)
            if res is not None:
                S, mul = res
                n, E = lib.group_lift(2, [(0, 1, s) for s in S], N, mul)
                consider(n, E)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
