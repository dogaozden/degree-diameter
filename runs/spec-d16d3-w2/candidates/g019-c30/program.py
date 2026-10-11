import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc helpers (fallback for D = 3)
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
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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
    """Incidence graph of PG(2,q) plus, per element of S, an A-vertex and a B-vertex."""
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
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _arc_candidates(d, deadline, rng):
    """For each prime power q with q + 1 <= d, build the best arc-extended PG(2,q) graph."""
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
# D = 3 via group Haar graphs.
#
# For a finite group G of order N and S subset of G with |S| = k, the Haar graph
# has parts A = G and B = G, with a_x ~ b_{xs} for s in S. It is k-regular and
# bipartite. Vertex-transitivity gives diameter <= 3 exactly when
#   S S^{-1} = G  (A-A distances <= 2)  and  S^{-1} S = G  (B-B distances <= 2),
# and mixed pairs are then within distance 3. For abelian G the two conditions
# coincide: S is a difference cover.
#
# Non-abelian groups Z_m x|_r Z_k give extra orders to search, beyond cyclic ones.
# We anneal S to cover all of G, and climb N upward from a high start.
# ----------------------------------------------------------------------------

def _groups_of_order(N, rng):
    """Candidate group descriptors of order N: the cyclic group, then semidirect products Z_m x| Z_k."""
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append(("s", m, k, r))
    rng.shuffle(cands)
    cands = cands[:10]
    return [("c", N)] + cands


def _tables(p):
    """Return (M, INV): full multiplication table and inverse list for a group descriptor."""
    if p[0] == "c":
        m = p[1]
        M = [[(a + b) % m for b in range(m)] for a in range(m)]
        INV = [(-a) % m for a in range(m)]
    else:
        order, mul, inv = lib.semidirect_group(p[1], p[2], p[3])
        M = [[mul(a, b) for b in range(order)] for a in range(order)]
        INV = [inv(a) for a in range(order)]
    return M, INV


def _cover(k, N, M, INV, rng, deadline):
    """Find S subset of G (|S| = k) with S S^{-1} = G and S^{-1} S = G. Returns sorted S, or None."""
    S = rng.sample(range(N), k)
    c1 = [0] * N  # counts of a * b^{-1} over ordered pairs in S
    c2 = [0] * N  # counts of a^{-1} * b over ordered pairs in S
    for a in S:
        for b in S:
            c1[M[a][INV[b]]] += 1
            c2[M[INV[a]][b]] += 1
    unc = sum(1 for g in range(N) if c1[g] == 0) + sum(1 for g in range(N) if c2[g] == 0)
    T = 1.0
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        T = max(0.05, T * 0.9999)
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(N)
        if y in S:
            continue
        others = S[:i] + S[i + 1:]
        rem1, rem2, add1, add2 = [], [], [], []
        for s in others:
            rem1.append(M[x][INV[s]])
            rem1.append(M[s][INV[x]])
            rem2.append(M[INV[x]][s])
            rem2.append(M[INV[s]][x])
            add1.append(M[y][INV[s]])
            add1.append(M[s][INV[y]])
            add2.append(M[INV[y]][s])
            add2.append(M[INV[s]][y])
        rem1.append(M[x][INV[x]])
        rem2.append(M[INV[x]][x])
        add1.append(M[y][INV[y]])
        add2.append(M[INV[y]][y])
        delta = 0
        for g in rem1:
            c1[g] -= 1
            if c1[g] == 0:
                delta += 1
        for g in rem2:
            c2[g] -= 1
            if c2[g] == 0:
                delta += 1
        for g in add1:
            if c1[g] == 0:
                delta -= 1
            c1[g] += 1
        for g in add2:
            if c2[g] == 0:
                delta -= 1
            c2[g] += 1
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            unc += delta
        else:
            for g in add1:
                c1[g] -= 1
            for g in add2:
                c2[g] -= 1
            for g in rem1:
                c1[g] += 1
            for g in rem2:
                c2[g] += 1
    return sorted(S)


def _group_haar_search(k, rng, deadline):
    """Climb the group order N upward from a high start; return (N, M, S) for the largest found, or None."""
    if k < 2:
        return None
    mmax = k * (k - 1) + 1  # counting bound, valid for any group
    N = max(k, int(0.8 * mmax))
    best = None
    fails = 0
    while N <= mmax and time.monotonic() < deadline:
        got = None
        for p in _groups_of_order(N, rng):
            now = time.monotonic()
            if now >= deadline:
                break
            slice_ = max(0.3, min(8.0, (deadline - now) / 4.0))
            M, INV = _tables(p)
            S = _cover(k, N, M, INV, rng, min(deadline, now + slice_))
            if S is not None:
                got = (N, M, S)
                break
        if got is not None:
            best = got
            fails = 0
        else:
            fails += 1
            if fails >= 2:
                break
        N += 1
    return best


def _group_haar_graph(N, M, S):
    """Haar graph over a group: a_x (vertex x) ~ b_{x s} (vertex N + M[x][s]) for s in S."""
    edges = [(x, N + M[x][s]) for x in range(N) for s in S]
    return 2 * N, edges


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4)
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

    if D == 3:
        # Primary: group Haar graph (cyclic or semidirect) with a two-sided cover.
        res = _group_haar_search(d, rng, start + 0.85 * budget)
        if res is not None:
            N, M, S = res
            n, E = _group_haar_graph(N, M, S)
            consider(n, E)
        else:
            # Secondary: arc-extended projective plane.
            cands = _arc_candidates(d, deadline, random.Random(seed * 7919 + d))
            cands.sort(key=lambda t: -t[0])
            for n_c, E_c, _side in cands[:1]:
                consider(n_c, E_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
