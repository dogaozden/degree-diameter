import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc-extension family (fallback, unchanged in spirit).
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
        n, E = _arc_graph(m, edges, point_lines, line_points, S)
        out.append((n, E))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
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
# NEW CONSTRUCTION: Haar graphs of finite groups with a difference cover.
#
# For a group G of order N and S subset of G with |S| = d, the Haar graph
# H(G, S) has parts a_x, b_x (x in G) and edges a_x -- b_{x s} for s in S.
# It is d-regular and bipartite on 2N vertices. Two a-vertices share a
# neighbour iff g = t s^{-1} for some s, t in S, and the cross pairs are then
# also within distance 3. So diameter <= 3 iff every non-identity g in G is
# of the form t s^{-1} (s != t). This is a difference-cover problem, searched
# here by simulated annealing over S. Cyclic and dihedral groups are tried.
# ----------------------------------------------------------------------------

def _group_tables(kind, N):
    """Return (mt, iv): full multiplication table and inverse list for a group of order N."""
    if kind == 'cyc':
        mt = [[(x + y) % N for y in range(N)] for x in range(N)]
        iv = [(-x) % N for x in range(N)]
    else:
        m = N // 2
        _, mul, inv = lib.semidirect_group(m, 2, m - 1)  # dihedral group of order 2m
        mt = [[mul(x, y) for y in range(N)] for x in range(N)]
        iv = [inv(x) for x in range(N)]
    return mt, iv


def _swap(S, i, y, cnt, mt, iv):
    """Replace S[i] by y, updating difference counts cnt; return change in #uncovered non-identity elements."""
    x = S[i]
    dunc = 0
    d = len(S)
    for j in range(d):
        if j == i:
            continue
        s = S[j]
        for g in (mt[x][iv[s]], mt[s][iv[x]]):
            cnt[g] -= 1
            if cnt[g] == 0:
                dunc += 1
    S[i] = y
    for j in range(d):
        if j == i:
            continue
        s = S[j]
        for g in (mt[y][iv[s]], mt[s][iv[y]]):
            if cnt[g] == 0:
                dunc -= 1
            cnt[g] += 1
    return dunc


def _cover_sa(N, d, mt, iv, rng, until):
    """Search S (|S| = d) in a group of order N whose differences cover G. Returns S or None."""
    S = rng.sample(range(N), d)
    cnt = [0] * N
    for s in S:
        for t in S:
            if s != t:
                cnt[mt[t][iv[s]]] += 1
    unc = sum(1 for g in range(1, N) if cnt[g] == 0)
    T = 0.35
    it = 0
    while unc > 0:
        it += 1
        if (it & 255) == 0 and time.monotonic() > until:
            return None
        i = rng.randrange(d)
        if rng.random() < 0.7:
            uncs = [g for g in range(1, N) if cnt[g] == 0]
            g = rng.choice(uncs)
            s = S[rng.randrange(d)]
            y = mt[g][s]  # then y * s^{-1} = g
        else:
            y = rng.randrange(N)
        if y in S:
            continue
        old = S[i]
        dunc = _swap(S, i, y, cnt, mt, iv)
        if dunc <= 0 or rng.random() < math.exp(-dunc / T):
            unc += dunc
        else:
            _swap(S, i, old, cnt, mt, iv)
    return S


def _haar_search(d, deadline, rng):
    """Climb the group order N upward; return (N, S, mt) for the largest N found, or None."""
    Nmax = d * (d - 1) + 1  # Moore-type bound: |S S^{-1}| <= d(d-1)+1
    found = None
    failed = None
    N = max(d + 1, Nmax // 2)
    while N <= Nmax:
        now = time.monotonic()
        if now >= deadline:
            break
        got = None
        for kind in ('cyc', 'dih'):
            if kind == 'dih' and (N % 2 or N // 2 < 3):
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            mt, iv = _group_tables(kind, N)
            until = min(deadline, now + max(0.5, 0.3 * (deadline - now)))
            S = _cover_sa(N, d, mt, iv, rng, until)
            if S is not None:
                got = (N, S, mt)
                break
        if got is None:
            failed = N
            break
        found = got
        N += 1
    # Spend leftover time on one more attempt at the first failing order.
    if failed is not None and time.monotonic() < deadline - 0.5:
        mt, iv = _group_tables('cyc', failed)
        S = _cover_sa(failed, d, mt, iv, rng, deadline)
        if S is not None:
            found = (failed, S, mt)
    return found


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
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

    if D >= 3:
        # Arc-extended projective-plane graphs (previous construction, as a fallback).
        arc_deadline = start + 0.3 * time_limit
        for n_c, E_c in _arc_candidates(d, arc_deadline, random.Random(seed * 7919 + d)):
            consider(n_c, E_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # New construction: Haar graphs of groups with difference covers (diameter <= 3).
    if D >= 3 and time.monotonic() < deadline:
        res = _haar_search(d, deadline, rng)
        if res is not None:
            N, S, mt = res
            n_h = 2 * N
            E_h = [(x, N + mt[x][s]) for x in range(N) for s in S]
            consider(n_h, E_h)

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
