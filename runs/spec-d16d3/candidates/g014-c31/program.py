import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base data.
# Base vertices: points 0..m-1, lines m..2m-1 (in the incidence graph).
# point_lines[P] = line indices through point P; line_points[L] = points on line L.
# ----------------------------------------------------------------------------

def _prime_powers_desc(x):
    return [q for q in range(x, 1, -1) if lib.is_prime_power(q)]


def _pg_data(q):
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


def _loads_ok(S, s, m, pl, lp):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl) <= s and max(cp) <= s


def _conic(q, index):
    """Conic (plus nucleus for even q) as a point-index set."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _random_arc(m, s, pl, lp, rng):
    """Random greedy set S with every line holding <= s points of S and every point on <= s S-lines."""
    order = list(range(m))
    rng.shuffle(order)
    cl = [0] * m
    cp = [0] * m
    S = []
    for P in order:
        if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
            S.append(P)
            for L in pl[P]:
                cl[L] += 1
            for Q in lp[P]:
                cp[Q] += 1
    return S


def _arc_graph(m, edges, pl, lp, S):
    """PG incidence plus an A-vertex per S-point (adjacent to its lines) and a B-vertex per S-line."""
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, J in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[J]:
            E.append((Q, b))
    return 2 * m + 2 * k, E


# ----------------------------------------------------------------------------
# NEW helper: pencil augmentation.
#
# A new point-side vertex v joined to all q+1 lines through a point P covers
# every point (distance 2) and every line (distance 3), and it is at distance
# <= 2 from every other point-side vertex (they share the line joining the
# two centres). The same holds dually for new line-side vertices joined to
# the q+1 points of a line. Each such vertex needs one spare degree on every
# line (or point) of its pencil, so we greedily pick centres whose pencils
# still fit into the spare capacity left after the arc vertices.
# ----------------------------------------------------------------------------

def _pencil_augment(m, n0, E0, pl, lp, S, s, rng, deadline):
    a = [0] * m
    for P in S:
        for L in pl[P]:
            a[L] += 1
    b = [0] * m
    for J in S:
        for Q in lp[J]:
            b[Q] += 1
    capL = [s - a[L] for L in range(m)]
    capP = [s - b[Q] for Q in range(m)]

    order = list(range(m))
    rng.shuffle(order)
    cen_pt = []
    for P in order:
        if time.monotonic() > deadline:
            break
        if all(capL[L] >= 1 for L in pl[P]):
            for L in pl[P]:
                capL[L] -= 1
            cen_pt.append(P)

    order = list(range(m))
    rng.shuffle(order)
    cen_ln = []
    for J in order:
        if time.monotonic() > deadline:
            break
        if all(capP[Q] >= 1 for Q in lp[J]):
            for Q in lp[J]:
                capP[Q] -= 1
            cen_ln.append(J)

    E = list(E0)
    n = n0
    for P in cen_pt:
        v = n
        n += 1
        for L in pl[P]:
            E.append((v, m + L))
    for J in cen_ln:
        w = n
        n += 1
        for Q in lp[J]:
            E.append((Q, w))
    return n, E


# ----------------------------------------------------------------------------
# Fallbacks and top-level search.
# ----------------------------------------------------------------------------

def _fallback(d, D):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    return lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2


def _solve(d, D, rng, start, deadline):
    best = _fallback(d, D)
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d < 3 or D < 3:
        return best

    for q in _prime_powers_desc(min(d - 1, 23)):
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, pl, lp, index = _pg_data(q)
        consider(2 * m, edges)
        if s == 0:
            continue

        seen = set()
        for t in range(60):
            if time.monotonic() > deadline:
                break
            S = None
            if t == 0 and s >= 2:
                cs = _conic(q, index)
                if _loads_ok(cs, s, m, pl, lp):
                    S = cs
            if S is None:
                S = _random_arc(m, s, pl, lp, rng)
            if not S:
                continue
            key = tuple(sorted(S))
            if key in seen:
                continue
            seen.add(key)
            n0, E0 = _arc_graph(m, edges, pl, lp, S)
            consider(n0, E0)
            n1, E1 = _pencil_augment(m, n0, E0, pl, lp, S, s, rng, deadline)
            consider(n1, E1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d, D)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)
    try:
        n, edges = _solve(d, D, rng, start, deadline)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return _fallback(d, D)
