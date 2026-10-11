import itertools
import random
import time

import lib

# ----------------------------------------------------------------------------
# D = 3 construction: PG(2,q) incidence graph with decoupled pencil vertices.
#
# Base: point-line incidence graph of PG(2,q), degree q+1, diameter 3.
# Spare degree s = d-q-1 is used by two independent kinds of new vertices:
#   * x_P for a point P in a set C: adjacent to all q+1 lines through P.
#     Every point shares a line with P, so x_P is within distance 2 of all
#     points and of every other x_P'. A line M gains one edge per centre P on
#     it, so C must satisfy: every line contains at most s points of C.
#   * y_L for a line L in a set D: adjacent to all q+1 points on L (dual).
#     D must satisfy: every point lies on at most s lines of D.
# Unlike the coupled arc construction (one set used on both sides), C and D are
# chosen independently. Each side is found by a plateau search that keeps the
# load bound and tries to grow the set. A final saturation pass adds any
# remaining point-line / pencil edges that fit in spare degree. Adding edges
# never increases distance, so the diameter bound is preserved.
# ----------------------------------------------------------------------------


def _pg(q):
    """Return (m, point_lines, line_points) for PG(2, q); points and lines are indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        L = v - m
        point_lines[u].append(L)
        line_points[L].append(u)
    return m, point_lines, line_points


def _bounded_set(inc, m, s, rng, deadline):
    """Largest set S (found heuristically) of elements 0..m-1 where each bin is hit by at most s members.

    inc[u] lists the bins of element u. Plateau search: random swaps that keep the bound,
    and direct additions whenever they fit.
    """
    if s <= 0:
        return []
    cnt = [0] * m
    in_s = [False] * m
    S = []

    def fits(u):
        for x in inc[u]:
            if cnt[x] >= s:
                return False
        return True

    def put(u):
        in_s[u] = True
        S.append(u)
        for x in inc[u]:
            cnt[x] += 1

    def take(u):
        in_s[u] = False
        S.remove(u)
        for x in inc[u]:
            cnt[x] -= 1

    order = list(range(m))
    rng.shuffle(order)
    for u in order:
        if fits(u):
            put(u)
    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() >= deadline:
            break
        u = rng.randrange(m)
        if in_s[u]:
            continue
        if fits(u):
            put(u)
            if len(S) > len(best):
                best = list(S)
            continue
        full = {x for x in inc[u] if cnt[x] >= s}
        cands = [w for w in S if any(x in full for x in inc[w])]
        if not cands:
            continue
        w = rng.choice(cands)
        take(w)
        if fits(u):
            put(u)
        else:
            put(w)
    return best


def _pencil_graph(m, point_lines, line_points, C, D):
    """Base incidence graph plus pencil vertices for C (side A) and dual pencils for D (side B)."""
    n = 2 * m + len(C) + len(D)
    sideA = [True] * m + [False] * m + [True] * len(C) + [False] * len(D)
    E = []
    for P in range(m):
        for L in point_lines[P]:
            E.append((P, m + L))
    for t, P in enumerate(C):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    base = 2 * m + len(C)
    for t, L in enumerate(D):
        y = base + t
        for P in line_points[L]:
            E.append((P, y))
    return n, E, sideA


def _saturate(n, E, d, sideA):
    """Greedily add any missing cross-side edge between vertices with spare degree.

    Adding edges never increases distances, so the diameter bound is kept.
    """
    deg = [0] * n
    have = set()
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
        have.add((u, v) if sideA[u] else (v, u))
    A = [u for u in range(n) if sideA[u]]
    B = [v for v in range(n) if not sideA[v]]
    out = list(E)
    for a in A:
        if deg[a] >= d:
            continue
        for b in B:
            if deg[a] >= d:
                break
            if deg[b] < d and (a, b) not in have:
                have.add((a, b))
                deg[a] += 1
                deg[b] += 1
                out.append((a, b))
    return out


def _build_q(q, d, deadline, rng):
    """Pencil-extended PG(2,q) graph for degree d, with spare s = d-q-1."""
    s = d - q - 1
    m, pl, lp = _pg(q)
    if s >= 1:
        now = time.monotonic()
        window = max(0.0, deadline - now)
        C = _bounded_set(pl, m, s, rng, now + 0.5 * window)
        D = _bounded_set(lp, m, s, rng, deadline)
    else:
        C, D = [], []
    n, E, sideA = _pencil_graph(m, pl, lp, C, D)
    E = _saturate(n, E, d, sideA)
    return n, E


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
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle: bipartite, degree 2, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D == 3:
        cands = []
        for q in range(2, d):
            if not lib.is_prime_power(q) or q + 1 > d:
                continue
            s = d - q - 1
            m = q * q + q + 1
            ub = 2 * m + (2 * s * m) // (q + 1)  # counting bound on the order
            cands.append((ub, q))
        cands.sort(reverse=True)
        for i, (ub, q) in enumerate(cands):
            if ub <= best_n:
                continue
            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0.05:
                break
            dl = now + remaining / (len(cands) - i)
            n, E = _build_q(q, d, dl, rng)
            consider(n, E)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
