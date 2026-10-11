import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base and helpers.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q); index maps vectors to ids."""
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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


# ----------------------------------------------------------------------------
# NEW: iterated local search for maximum "load-bounded" arcs.
#
# A set S of indices (valid as both points and lines of PG(2, q)) is feasible
# when every line contains <= s points of S and every point lies on <= s
# lines indexed by S. The search repeatedly removes 1-3 random members and
# greedily refills in a random order, accepting moves that do not shrink S.
# ----------------------------------------------------------------------------

def _loads(S, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return cl, cp


def _refill(S, s, m, point_lines, line_points, rng):
    """Greedily extend the feasible set S with the other indices, in random order."""
    cl, cp = _loads(S, m, point_lines, line_points)
    inS = set(S)
    order = [P for P in range(m) if P not in inS]
    rng.shuffle(order)
    out = list(S)
    for P in order:
        if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
            out.append(P)
            for L in point_lines[P]:
                cl[L] += 1
            for Q in line_points[P]:
                cp[Q] += 1
    return out


def _ils_arc(m, s, point_lines, line_points, rng, seed_set, deadline):
    """Iterated local search for a large feasible set; returns the best set found."""
    cur = _refill(list(seed_set), s, m, point_lines, line_points, rng)
    best = cur
    while time.monotonic() < deadline:
        k = rng.randint(1, 3)
        base = list(cur)
        for _ in range(min(k, len(base))):
            base.pop(rng.randrange(len(base)))
        cand = _refill(base, s, m, point_lines, line_points, rng)
        if len(cand) >= len(cur):
            cur = cand
            if len(cur) > len(best):
                best = cur
    return best


def _arc_candidates(d, deadline, rng):
    """One ILS-optimised arc-extended graph per prime power q with spare s = d - q - 1 >= 1."""
    qs = [q for q in range(2, min(d - 1, 23) + 1)
          if lib.is_prime_power(q) and d - q - 1 >= 1]
    out = []
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now >= deadline:
            break
        dl = now + (deadline - now) / (len(qs) - idx)  # share the remaining budget evenly
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        F = lib.GF(q)
        cs = _conic_set(q, index, F)
        seed = cs if _loads_ok(cs, s, m, point_lines, line_points) else []
        S = _ils_arc(m, s, point_lines, line_points, rng, seed, dl)
        if S and _loads_ok(S, s, m, point_lines, line_points):
            out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        for n_c, e_c in _arc_candidates(d, start + 0.8 * time_limit, rng):
            consider(n_c, e_c)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
