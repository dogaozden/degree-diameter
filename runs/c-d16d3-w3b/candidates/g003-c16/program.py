import random
import time

import lib

# ----------------------------------------------------------------------------
# Star-extension of projective planes (diameter 3), a different construction
# from the voltage-lift search.
#
# Start from PG(2, q) incidence: points 0..m-1, lines m..2m-1, degree q+1.
# With spare s = d - (q+1), add two families of new vertices:
#   A-star(P): a new point-side vertex joined to all q+1 lines through P.
#   B-star(L): a new line-side vertex joined to all q+1 points on L.
# A-stars use spare on lines, B-stars use spare on points, so the two
# families are independent. Each line may carry at most s A-stars (its
# A-center points must form a set with <= s centers per line), and each
# point at most s B-stars, which is the same capacitated-set problem.
#
# Diameter check (why this stays within 3 for any choice of centers):
#   A-star to A-star: common line of the two centers, length 2.
#   B-star to B-star: common point of the two lines, length 2.
#   A-star x_P to point X: via line PX, length 2.
#   A-star x_P to B-star y_L: x_P - M - (M cap L) - y_L, length 3.
#   A-star x_P to line L: x_P - M - (M cap L) - L, length 3, or 1 if P on L.
# Every candidate is still checked with lib.is_valid before acceptance.
#
# With s = 2 and q = 13 the centers form a conic (an arc), giving 14 + 14
# new vertices, order 2*183 + 28 = 394. Integer capacitated sets cannot
# beat an arc here, so this family reaches the record but does not beat it.
# ----------------------------------------------------------------------------


def _pg(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _loads_ok(S, cap, nbr, m):
    """True if every target is hit by at most cap elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
            if load[t] > cap:
                return False
    return True


def _arc(q, pts):
    """Conic plus nucleus (q even): an arc, so each line meets it in <= 2 points.

    The same index set is also a dual arc when read as lines, because lib uses the
    same coordinate vectors for points and lines.
    """
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _greedy(m, cap, nbr, rng, deadline, trials):
    """Randomized greedy capacitated set; keeps the largest result over the trials."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < cap for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _best_set(m, cap, nbr, arc, rng, deadline):
    """Largest valid capacitated set among greedy and the algebraic arc."""
    cands = [_greedy(m, cap, nbr, rng, deadline, 200)]
    if arc is not None and _loads_ok(arc, cap, nbr, m):
        cands.append(list(arc))
    return max(cands, key=len)


def _star_graph(q, d, rng, deadline):
    """Return (n, edges) for PG(2,q) plus stars, or None if q + 1 > d."""
    s = d - (q + 1)
    if s < 0:
        return None
    m, edges, point_lines, line_points = _pg(q)
    pts = lib.projective_points(q)
    arc = _arc(q, pts)
    SA = _best_set(m, s, point_lines, arc, rng, deadline)  # centers of A-stars (points)
    SB = _best_set(m, s, line_points, arc, rng, deadline)  # centers of B-stars (lines)
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, L in enumerate(SB):
        y = 2 * m + na + t
        for Q in line_points[L]:
            E.append((Q, y))
    return n, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        qs = [q for q in range(2, min(d, 24)) if lib.is_prime_power(q)]
        qs.sort(reverse=True)
        for idx, q in enumerate(qs):
            now = time.monotonic()
            if now > deadline:
                break
            q_deadline = now + (deadline - now) / (len(qs) - idx)
            cand = _star_graph(q, d, rng, q_deadline)
            if cand is not None:
                consider(cand[0], cand[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
