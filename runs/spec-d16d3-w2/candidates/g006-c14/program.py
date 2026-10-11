import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc construction (safe fallback for D = 3, the parent's record)
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
# New D = 3 construction: bi-Cayley graphs over (possibly non-abelian) groups.
#
# For a group G of order N and a k-subset S, let B(G,S) have parts A = G and
# B = G with a ~ b iff b = a*s for some s in S. It is k-regular and bipartite,
# with 2N vertices. Pairs in A are within distance 2 iff every g != e is of the
# form s*t^{-1}; pairs in B are within distance 2 iff every g != e is of the
# form s^{-1}*t. Mixed pairs are then within distance 3 automatically. So
# diameter 3 holds exactly when S S^{-1} = G and S^{-1} S = G.
# We search for such S by annealing over several groups of each order N,
# and climb N upward from just above the current best (order 2N > best).
# ----------------------------------------------------------------------------

def _cyclic_tables(N):
    T = [[(x + y) % N for y in range(N)] for x in range(N)]
    I = [(-x) % N for x in range(N)]
    return T, I


def _tables(order, mul, inv):
    T = [[mul(x, y) for y in range(order)] for x in range(order)]
    I = [inv(x) for x in range(order)]
    return T, I


def _groups_of_order(N, rng, max_groups=3):
    """Cyclic group of order N plus a few semidirect products Z_a x| Z_b with a*b = N."""
    groups = [_cyclic_tables(N)]
    cand = []
    for b in range(2, N):
        if N % b:
            continue
        a = N // b
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a:
                cand.append((a, b, r))
    rng.shuffle(cand)
    for a, b, r in cand[: max_groups - 1]:
        try:
            order, mul, inv = lib.semidirect_group(a, b, r)
        except ValueError:
            continue
        if order == N:
            groups.append(_tables(order, mul, inv))
    return groups


def _upd(T, I, cL, cR, x, others, sgn):
    """Add (sgn=+1) or remove (sgn=-1) all ordered pairs involving x; return change in zero-count."""
    dz = 0
    Ix = I[x]
    for t in others:
        It = I[t]
        for arr, g in ((cL, T[x][It]), (cR, T[Ix][t]), (cL, T[t][Ix]), (cR, T[It][x])):
            c = arr[g]
            if sgn < 0:
                arr[g] = c - 1
                if c == 1:
                    dz += 1
            else:
                arr[g] = c + 1
                if c == 0:
                    dz -= 1
    return dz


def _anneal(T, I, N, k, rng, deadline):
    """Find S, |S| = k, with S S^{-1} = G = S^{-1} S (identity excluded). Returns sorted S or None."""
    if N <= k:
        return None
    S = rng.sample(range(N), k)
    inS = [False] * N
    for s in S:
        inS[s] = True
    cL = [0] * N
    cR = [0] * N
    for a in S:
        for b in S:
            if a != b:
                cL[T[a][I[b]]] += 1
                cR[T[I[a]][b]] += 1
    cost = sum(1 for g in range(1, N) if cL[g] == 0) + sum(1 for g in range(1, N) if cR[g] == 0)
    temp = rng.choice((0.3, 0.45, 0.6))
    it = 0
    while cost > 0:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(N)
        if inS[y]:
            continue
        others = S[:i] + S[i + 1:]
        dz = _upd(T, I, cL, cR, x, others, -1) + _upd(T, I, cL, cR, y, others, 1)
        if dz <= 0 or rng.random() < math.exp(-dz / temp):
            S[i] = y
            inS[x] = False
            inS[y] = True
            cost += dz
        else:
            _upd(T, I, cL, cR, y, others, -1)
            _upd(T, I, cL, cR, x, others, 1)
    return sorted(S)


def _bicayley(T, N, S):
    """Bipartite graph: a in A (vertex a) joined to b = a*s (vertex N + a*s) for s in S."""
    E = []
    for a in range(N):
        Ta = T[a]
        for s in S:
            E.append((a, N + Ta[s]))
    return 2 * N, E


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
    budget = min(0.8 * float(time_limit), 45.0)
    search_end = start + budget
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
        # Secondary (safe): arc-extended projective plane, known to give the parent's record.
        cands = _arc_candidates(d, start + 0.3 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands[:1]:
            consider(n_c, E_c)

        # Primary (bold): bi-Cayley graphs from difference covers over groups of order N.
        # Order of the graph is 2N, so start just above the current best half-order.
        k = d
        if k >= 2:
            mmax = k * (k - 1) + 1
            m = max(k + 1, best_n // 2 + 1)
            fails = 0
            while m <= mmax and time.monotonic() < search_end and fails < 2:
                remaining = search_end - time.monotonic()
                cap = time.monotonic() + max(2.0, 0.4 * remaining)
                found = None
                groups = _groups_of_order(m, rng)
                while found is None and time.monotonic() < cap:
                    for T, I in groups:
                        now = time.monotonic()
                        if now >= cap:
                            break
                        slice_end = min(cap, now + 3.0)
                        S = _anneal(T, I, m, k, rng, slice_end)
                        if S is not None:
                            found = (T, S)
                            break
                if found is not None:
                    T, S = found
                    n, E = _bicayley(T, m, S)
                    consider(n, E)
                    fails = 0
                else:
                    fails += 1
                m += 1

    if D >= 4 and time.monotonic() < search_end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
