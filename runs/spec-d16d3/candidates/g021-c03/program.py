import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases
# ----------------------------------------------------------------------------

def _best_pg_q(d):
    """Largest prime power q with q + 1 <= d (PG(2, q) incidence has degree q + 1)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q). Points and lines share indices 0..m-1."""
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
# New construction: asymmetric conic twin extension of PG(2, q).
#
# A-vertex per point P of SA, joined to the q+1 lines through P.
# B-vertex per line L of SB, joined to the q+1 points on L.
# Diameter stays 3 for ANY SA, SB (checked by distance case analysis), so
# SA and SB may be chosen independently. Loads: each line may contain at most
# s points of SA, and each point may lie on at most s lines of SB.
# Conics are arcs and their duals are dual arcs, so they satisfy the loads
# with s = 2. Different conics give different extensions of the same base.
# ----------------------------------------------------------------------------

def _parabola(q, F, index, a, b):
    """Conic {(1, t, a t^2 + b t) : t} plus (0, 0, 1), for a != 0. It is a (q+1)-arc."""
    S = []
    for t in range(q):
        y = F.add(F.mul(a, F.mul(t, t)), F.mul(b, t))
        S.append(index[(1, t, y)])
    S.append(index[(0, 0, 1)])
    return S


def _loads_ok(SA, SB, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in SA:
        for L in point_lines[P]:
            cl[L] += 1
    for L in SB:
        for Q in line_points[L]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _asym_graph(m, edges, point_lines, line_points, SA, SB):
    """PG(2,q) incidence plus A-vertices (for SA) and B-vertices (for SB)."""
    k, l = len(SA), len(SB)
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, L in enumerate(SB):
        b = 2 * m + k + t
        for Q in line_points[L]:
            E.append((Q, b))
    return 2 * m + k + l, E


# ----------------------------------------------------------------------------
# Cover-based vertex growth (any diameter D).
#
# A new vertex v on side c with neighbour set U (all on the opposite side, all
# with spare degree) keeps diameter <= D iff the radius-(D-1) balls of U cover
# every vertex. Adding vertices never lengthens existing shortest paths, so
# the invariant is preserved. We also add the new vertex on the side with a
# valid cover.
# ----------------------------------------------------------------------------

def _balls(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        nxt = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt.append(x)
        ball = nxt
    return ball


def _colors(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate balls; None if it fails."""
    pool = list(cands)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains)
        if best_g <= 0:
            break
        if randomize:
            thr = best_g - 1 if (best_g > 1 and rng.random() < 0.3) else best_g
            opts = [i for i, g in enumerate(gains) if g >= thr]
            i = rng.choice(opts)
        else:
            i = gains.index(best_g)
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _grow(n, edges, d, D, deadline, rng, tries=60):
    edges = [tuple(e) for e in edges]
    if D < 2:
        return n, edges
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _colors(n, adj)
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and len(adj[s]) < d]
            if not cands:
                continue
            chosen = None
            for t in range(tries):
                if time.monotonic() >= deadline:
                    break
                chosen = _cover(cands, ball, full, d, rng, t > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                adj.append([])
                color.append(1 - c)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                added = True
                break
        if not added:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])
    if d == 2:
        n = 2 * D  # even cycle: bipartite, degree 2, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} (diameter 2).
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        # 1. Plain projective plane, grown by cover vertices.
        q0 = _best_pg_q(d)
        if q0 is not None:
            n0, e0 = lib.projective_plane_incidence(q0)
            consider(n0, e0)
            consider(*_grow(n0, e0, d, D, start + 0.08 * time_limit, rng))

        # 2. Araujo-Pardo & Lopez style graph (degree q+2 <= d) with cover growth.
        qa = [q for q in range(3, d - 1) if lib.is_prime_power(q)]
        if qa:
            try:
                n1, e1 = lib.araujo_lopez_graph(qa[-1])
                consider(n1, e1)
                consider(*_grow(n1, e1, d, D, start + 0.2 * time_limit, rng))
            except ValueError:
                pass

        # 3. Asymmetric conic twin extensions of PG(2, q), with cover growth.
        #    The first sample is the symmetric conic (parent's arc record);
        #    later samples use independent conics for SA and SB.
        qc = [q for q in range(2, d - 2) if lib.is_prime_power(q)]
        if qc:
            q = qc[-1]
            s = d - q - 1
            m, edges, pl, lp, index = _pg_data(q)
            F = lib.GF(q)
            conics = [_parabola(q, F, index, a, b)
                      for a in range(1, q) for b in range(q)]
            first = True
            while time.monotonic() < deadline:
                if first:
                    SA = SB = conics[0]
                    first = False
                else:
                    SA = rng.choice(conics)
                    SB = rng.choice(conics)
                if not _loads_ok(SA, SB, s, m, pl, lp):
                    continue
                n, e = _asym_graph(m, edges, pl, lp, SA, SB)
                consider(n, e)
                slice_end = min(deadline, time.monotonic() + 3.0)
                consider(*_grow(n, e, d, D, slice_end, rng))

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            consider(*_grow(gq[0], gq[1], d, D, start + 0.9 * time_limit, rng))

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
