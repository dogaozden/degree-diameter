import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold alternative: arc-extended projective plane graphs (diameter 3), found by
# a local search over (k, s)-arcs instead of a single greedy pass.
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 each has spare s = d-q-1.
# Choose S (point indices, also read as line indices by polarity) so that every
# line holds <= s points of S and every point lies on <= s lines indexed by S.
# Then add an A-vertex per P in S (joined to the q+1 lines through P) and a
# B-vertex per j in S (joined to the q+1 points on line j). Old vertices stay
# within degree d. Distances stay <= 3, and the result is checked anyway.
#
# Saturation adds any missing point-line and A-B edges with spare degree; this
# keeps the graph bipartite and never increases a distance.
#
# Every candidate is verified with lib.is_valid before it is kept. A K_{d,d}
# fallback (diameter 2) and the generalized quadrangle W(q) (diameter 4) cover
# the other diameters. Only the d=16, D=3 target and the d=3, D=3 calibration
# are targeted here, so other diameters use these simpler fallbacks.
# ----------------------------------------------------------------------------


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = {}
    cp = {}
    for P in S:
        for L in point_lines[P]:
            cl[L] = cl.get(L, 0) + 1
        for Q in line_points[P]:
            cp[Q] = cp.get(Q, 0) + 1
    return max(cl.values(), default=0) <= s and max(cp.values(), default=0) <= s


def _arc_local(m, s, PL, LP, rng, deadline, iters):
    """Local search for a large S with all loads <= s. Adds a random point and evicts the few blockers."""
    onl = [set() for _ in range(m)]   # S-points lying on line L
    onp = [set() for _ in range(m)]   # S-lines passing through point Q
    inS = [False] * m
    S = set()

    def add(P):
        S.add(P)
        inS[P] = True
        for L in PL[P]:
            onl[L].add(P)
        for Q in LP[P]:
            onp[Q].add(P)

    def rem(P):
        S.discard(P)
        inS[P] = False
        for L in PL[P]:
            onl[L].discard(P)
        for Q in LP[P]:
            onp[Q].discard(P)

    order = list(range(m))
    rng.shuffle(order)
    for P in order:
        if all(len(onl[L]) < s for L in PL[P]) and all(len(onp[Q]) < s for Q in LP[P]):
            add(P)
    best = set(S)

    for _ in range(iters):
        if time.monotonic() > deadline:
            break
        p = rng.randrange(m)
        if inS[p]:
            continue
        block = set()
        for L in PL[p]:
            if len(onl[L]) >= s:
                block |= onl[L]
        for Q in LP[p]:
            if len(onp[Q]) >= s:
                block |= onp[Q]
        k = len(block)
        # 0 blockers: strict gain. 1: plateau move. 2: rare downhill move. More: reject.
        if k >= 3 or (k == 2 and rng.random() > 0.05):
            continue
        for P in block:
            rem(P)
        add(p)
        if len(S) > len(best):
            best = set(S)
    return sorted(best)


def _best_arc(m, s, PL, LP, rng, deadline):
    """Restart the local search until the deadline and keep the largest arc."""
    best = []
    first = True
    while first or time.monotonic() < deadline:
        first = False
        sub = random.Random(rng.randrange(1 << 30))
        S = _arc_local(m, s, PL, LP, sub, deadline, iters=30000)
        if len(S) > len(best) and _loads_ok(S, s, PL, LP):
            best = S
        if time.monotonic() >= deadline:
            break
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, LP, S):
    """Old PG incidence plus a new A-vertex per P in S and a new B-vertex per j in S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    PL_S = None  # placeholder for clarity; A-vertices use point-line incidence below
    return n, E, k


def _attach_arc(m, edges, PL, LP, S):
    """Build the extended graph: old PG incidence plus A and B vertices for S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in PL[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in LP[j]:
            E.append((Q, b))
    return n, E


def _saturate(n, edges, m, k, d, rng):
    """Add every missing X-Y edge while both endpoints have spare degree <= d.

    X side: old points 0..m-1 and new A-vertices 2m..2m+k-1.
    Y side: old lines m..2m-1 and new B-vertices 2m+k..2m+2k-1.
    Adding X-Y edges keeps the graph bipartite and never increases a distance.
    """
    E = set()
    for u, v in edges:
        E.add((u, v) if u < v else (v, u))
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    X = [v for v in range(n) if v < m or 2 * m <= v < 2 * m + k]
    Y = [v for v in range(n) if m <= v < 2 * m or v >= 2 * m + k]
    spare_x = [v for v in X if deg[v] < d]
    spare_y = [v for v in Y if deg[v] < d]
    pairs = [(x, y) for x in spare_x for y in spare_y]
    rng.shuffle(pairs)
    for x, y in pairs:
        if deg[x] >= d or deg[y] >= d:
            continue
        key = (x, y) if x < y else (y, x)
        if key in E:
            continue
        E.add(key)
        deg[x] += 1
        deg[y] += 1
    return n, sorted(E)


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Arc-extended PG(2,q) graphs, diameter 3, valid for D >= 3.
    if D >= 3:
        arc_deadline = start + 0.5 * time_limit
        qs = [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)]
        for idx, q in enumerate(qs):
            now = time.monotonic()
            if now >= arc_deadline:
                break
            qdl = now + (arc_deadline - now) / (len(qs) - idx)
            m, edges, PL, LP, index = _pg_data(q)
            s = d - q - 1
            cands = [[]]
            if s >= 1:
                cands.append(_best_arc(m, s, PL, LP, rng, qdl))
            if s >= 2:
                F = lib.GF(q)
                cs = _conic_set(q, index, F)
                if _loads_ok(cs, s, PL, LP):
                    cands.append(cs)
            S = max(cands, key=len)
            if not _loads_ok(S, s, PL, LP):
                S = []
            n_c, e_c = _attach_arc(m, edges, PL, LP, S)
            n_c, e_c = _saturate(n_c, e_c, m, len(S), d, rng)
            consider(n_c, e_c)

    # Generalized quadrangle for diameter 4 (and above, since diameter <= 4 holds).
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
