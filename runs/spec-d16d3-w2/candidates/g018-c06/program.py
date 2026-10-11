import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# PG(2,q) arc-extension construction (D = 3 baseline, from the parent)
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
# New D = 3 construction: bipartite Cayley-type graphs over arbitrary small groups.
#
# For a finite group G of order N and S subset of G with |S| = k, let
#   A = G x {0}, B = G x {1}, and join (x,0) ~ (x s,1) for s in S.
# This is k-regular and bipartite with 2N vertices. Its diameter is at most 3
# when S S^{-1} = G and S^{-1} S = G (A-A pairs need S S^{-1}, B-B pairs need
# S^{-1} S, and mixed pairs follow from S S^{-1} = G). Since |S S^{-1}| is at
# most k(k-1)+1, we need N <= k(k-1)+1, so the order is capped at 2(k^2-k+1).
#
# The search climbs N upward from the current record/2, trying cyclic and
# semidirect products Z_m x| Z_k. Each attempt is a simulated anneal on the
# number of uncovered group elements for both coverage conditions.
# ----------------------------------------------------------------------------

def _group_tables(order, mul, inv):
    """Multiplication table M[x][y] and inverse table I[x] for a group on 0..order-1 (identity 0)."""
    M = [[mul(x, y) for y in range(order)] for x in range(order)]
    I = [inv(x) for x in range(order)]
    return M, I


def _contrib(x, others, M, I):
    """Index lists touched when element x is in S alongside the elements in others."""
    xi = I[x]
    L1 = []
    L2 = []
    for t in others:
        L1.append(M[x][I[t]])   # x t^{-1}
        L1.append(M[t][xi])     # t x^{-1}
        L2.append(M[xi][t])     # x^{-1} t
        L2.append(M[I[t]][x])   # t^{-1} x
    return L1, L2


def _dec(c, idxs, unc):
    """Decrement counters; track how many non-identity elements become uncovered."""
    for g in idxs:
        c[g] -= 1
        if c[g] == 0 and g:
            unc += 1
    return unc


def _inc(c, idxs, unc):
    """Increment counters; track how many non-identity elements become covered."""
    for g in idxs:
        if c[g] == 0 and g:
            unc -= 1
        c[g] += 1
    return unc


def _anneal(N, M, I, k, rng, deadline):
    """Find S subset of G, |S| = k, with S S^{-1} = G and S^{-1} S = G. Returns sorted S or None."""
    if k > N:
        return None
    S = rng.sample(range(N), k)
    inS = [False] * N
    for s in S:
        inS[s] = True
    c1 = [0] * N
    c2 = [0] * N
    for i in range(k):
        for j in range(k):
            if i != j:
                c1[M[S[i]][I[S[j]]]] += 1
                c2[M[I[S[i]]][S[j]]] += 1
    unc = sum(1 for g in range(1, N) if c1[g] == 0) + sum(1 for g in range(1, N) if c2[g] == 0)
    T = 0.8
    it = 0
    while unc > 0:
        it += 1
        if (it & 255) == 0:
            if time.monotonic() > deadline:
                return None
            T = max(0.12, T * 0.995)
            if it % 200000 == 0:
                T = 0.8
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(N)
        if inS[y]:
            continue
        others = [S[j] for j in range(k) if j != i]
        Lx1, Lx2 = _contrib(x, others, M, I)
        Ly1, Ly2 = _contrib(y, others, M, I)
        old = unc
        unc = _dec(c1, Lx1, unc)
        unc = _dec(c2, Lx2, unc)
        unc = _inc(c1, Ly1, unc)
        unc = _inc(c2, Ly2, unc)
        delta = unc - old
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            inS[x] = False
            inS[y] = True
        else:
            unc = _dec(c1, Ly1, unc)
            unc = _dec(c2, Ly2, unc)
            unc = _inc(c1, Lx1, unc)
            unc = _inc(c2, Lx2, unc)
    return sorted(S)


def _groups_for(N, rng):
    """Candidate groups of order N: the cyclic group (m=None) plus a few semidirect products Z_m x| Z_k."""
    out = [(None, None, None)]
    opts = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    rng.shuffle(opts)
    return out + opts[:6]


def _haar_group_graph(N, M, S):
    """Bipartite graph on 2N vertices: (x,0) = x joined to (x s,1) = N + x s for s in S."""
    E = []
    for s in S:
        for x in range(N):
            E.append((x, N + M[x][s]))
    return 2 * N, E


def _group_search(start_n, d, D, rng, deadline):
    """Ascending search over group orders N; returns the largest valid (n, edges) found, or None."""
    cap = d * (d - 1) + 1
    best = None
    N = start_n // 2 + 1
    fails = 0
    while N <= cap and fails < 2 and time.monotonic() < deadline:
        groups = _groups_for(N, rng)
        t_end = min(deadline, time.monotonic() + 6.0)
        found = None
        for gi, (m, k, r) in enumerate(groups):
            now = time.monotonic()
            if now >= t_end:
                break
            per = (t_end - now) / (len(groups) - gi)
            if m is None:
                order, mul, inv = lib.cyclic_group(N)
            else:
                order, mul, inv = lib.semidirect_group(m, k, r)
            M, I = _group_tables(order, mul, inv)
            S = _anneal(order, M, I, d, rng, time.monotonic() + per)
            if S is not None:
                found = (order, M, S)
                break
        if found is not None:
            order, M, S = found
            n, E = _haar_group_graph(order, M, S)
            if lib.is_valid(n, E, d, D):
                best = (n, E)
                fails = 0
            else:
                fails += 1
        else:
            fails += 1
        N += 1
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4, from the parent)
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

    if D == 3 and d >= 2:
        # Secondary baseline: arc-extended projective plane.
        cands = _arc_candidates(d, start + 0.25 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands[:1]:
            consider(n_c, E_c)
        # Primary: group-based bipartite Cayley graphs with diameter 3.
        res = _group_search(best_n, d, D, rng, deadline)
        if res is not None:
            consider(res[0], res[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
