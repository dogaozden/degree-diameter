import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc helpers (D = 3 construction from the parent)
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
# New construction for D = 3: Cayley bipartite graphs over NON-abelian groups.
#
# Let G be a group of order N and S a k-subset. The bipartite graph has
# A-vertices x and B-vertices y in G, with a_x ~ b_{x s} for s in S. It is
# k-regular. Using right differences R = {s t^-1 : s != t} and left
# differences L = {s^-1 t : s != t}:
#   * A-A distance <= 2 for all pairs  iff  R covers G \ {e},
#   * B-B distance <= 2 for all pairs  iff  L covers G \ {e},
#   * mixed pairs are then within distance 3 (since R + s0 covers G).
# Cyclic groups are the parent's Haar graphs. Semidirect products Z_m x| Z_k
# give more group choices at the same order, so a search over
# (group, S) can reach orders the cyclic search misses. Annealing minimises
# the number of uncovered elements of R and L together.
# Final validity is still checked with lib.is_valid.
# ----------------------------------------------------------------------------

def _group_options(N, rng):
    """Candidate groups of order N: cyclic Z_N first, then up to three semidirect products."""
    opts = []
    for kk in range(2, N):
        if N % kk:
            continue
        m = N // kk
        if m < 3:
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m]
        if rs:
            rng.shuffle(rs)
            opts.append(("s", m, kk, rs[0]))
    rng.shuffle(opts)
    return [("c", N)] + opts[:3]


def _group_tables(opt):
    """Return (order, mul table, inverse list) for a group option."""
    if opt[0] == "c":
        order, mul, inv = lib.cyclic_group(opt[1])
    else:
        order, mul, inv = lib.semidirect_group(opt[1], opt[2], opt[3])
    M = [[mul(x, y) for y in range(order)] for x in range(order)]
    I = [inv(x) for x in range(order)]
    return order, M, I


def _anneal_cover(N, M, I, k, rng, deadline):
    """Find a k-subset S of a group (identity coded 0) with R and L both covering all non-identity elements."""
    if N < k:
        return None
    S = rng.sample(range(N), k)
    inS = set(S)
    cR = [0] * N
    cL = [0] * N
    for a in S:
        for b in S:
            if a != b:
                cR[M[a][I[b]]] += 1
                cL[M[I[a]][b]] += 1
    unc = sum(1 for g in range(1, N) if cR[g] == 0) + sum(1 for g in range(1, N) if cL[g] == 0)

    def upd(a, others, sign):
        """Add (sign=+1) or remove (sign=-1) the difference pairs between a and each other; return change in uncovered count."""
        dlt = 0
        Ia = I[a]
        for s in others:
            Is = I[s]
            for c, g in ((cR, M[a][Is]), (cR, M[s][Ia]), (cL, M[Ia][s]), (cL, M[Is][a])):
                if g == 0:
                    continue
                if sign < 0:
                    c[g] -= 1
                    if c[g] == 0:
                        dlt += 1
                else:
                    if c[g] == 0:
                        dlt -= 1
                    c[g] += 1
        return dlt

    T = 0.5
    it = 0
    while unc > 0:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(N)
        if y in inS:
            continue
        others = S[:i] + S[i + 1:]
        d1 = upd(x, others, -1)
        d2 = upd(y, others, 1)
        delta = d1 + d2
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            inS.discard(x)
            inS.add(y)
            unc += delta
        else:
            upd(y, others, -1)
            upd(x, others, 1)
    return sorted(S)


def _cayley_search(k, rng, deadline, lo):
    """Search orders N from k(k-1)+1 down to lo+1; return (N, M, S) for the first success, or None."""
    N = k * (k - 1) + 1
    while N > lo and N >= k and time.monotonic() < deadline:
        now = time.monotonic()
        slice_total = max(0.2, (deadline - now) / (N - lo))
        opts = _group_options(N, rng)
        for opt in opts:
            order, M, I = _group_tables(opt)
            until = min(deadline, time.monotonic() + slice_total / len(opts))
            S = _anneal_cover(order, M, I, k, rng, until)
            if S is not None:
                return order, M, S
        N -= 1
    return None


def _cayley_graph(N, M, S):
    """Bipartite Cayley graph: a_x (vertex x) joined to b_{x s} (vertex N + x s) for s in S."""
    E = []
    for x in range(N):
        for s in S:
            E.append((x, N + M[x][s]))
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
        # Arc-extended projective planes (parent construction) give a strong baseline.
        cands = _arc_candidates(d, start + 0.3 * budget, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, E_c, _side in cands[:2]:
            consider(n_c, E_c)

        # New: Cayley bipartite graphs over cyclic and semidirect groups,
        # searching only for orders that would beat the current best.
        lo = best_n // 2
        res = _cayley_search(d, rng, start + 0.95 * budget, lo)
        if res is not None:
            N, M, S = res
            n_c, E_c = _cayley_graph(N, M, S)
            consider(n_c, E_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
