import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base and its dual-symmetric extension.
#
# Points 0..m-1, lines m..2m-1 (lib.projective_plane_incidence). With spare
# s = d - (q+1) on every vertex, choose a point set S_A and a line set S_B:
#   - each A-vertex for x in S_A joins the q+1 lines through x,
#   - each B-vertex for y in S_B joins the q+1 points on y.
# Load limits: every line meets S_A in <= s points, every point lies on <= s
# lines of S_B. The two sets are chosen INDEPENDENTLY, which the parent did not
# do (it forced S_A = S_B). Distances stay <= 3: any two points share a line,
# any two lines share a point, and A_x to B_y is always distance 3.
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


def _loads_ok(S, cap, m, pl):
    """True if no item of range(m) is hit by more than cap elements of S (pl[x] = items of x)."""
    counts = [0] * m
    for x in S:
        for t in pl[x]:
            counts[t] += 1
    return max(counts, default=0) <= cap


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear, valid for cap 2."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _max_set(m, cap, pl, rng, deadline, iters):
    """Random-walk local search for a large set S with every item loaded <= cap.

    Moves: insert a random element; if that overloads items, evict one blocker per
    overloaded item, but only when at most one eviction is needed (plateau moves).
    """
    pls = [set(x) for x in pl]
    load = [0] * m
    S = set()
    best = []
    for it in range(iters):
        if it & 127 == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if x in S:
            continue
        R = []
        for L in pl[x]:
            if load[L] >= cap:
                if any(L in pls[q] for q in R):
                    continue
                cands = [q for q in S if L in pls[q]]
                R.append(rng.choice(cands))
        if len(R) > 1:
            continue
        for q in R:
            S.discard(q)
            for L in pl[q]:
                load[L] -= 1
        if all(load[L] < cap for L in pl[x]):
            S.add(x)
            for L in pl[x]:
                load[L] += 1
            if len(S) > len(best):
                best = list(S)
        else:
            for q in R:
                S.add(q)
                for L in pl[q]:
                    load[L] += 1
    return best


def _best_side(m, cap, pl, conic, rng, deadline):
    """Best set for one side: conic if admissible, plus a few local-search restarts."""
    cands = []
    if conic is not None and _loads_ok(conic, cap, m, pl):
        cands.append(conic)
    for _ in range(3):
        if time.monotonic() > deadline:
            break
        cands.append(_max_set(m, cap, pl, rng, deadline, 40000))
    return max(cands, key=len, default=[])


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """PG incidence plus one new vertex per element of SA (point side) and SB (line side)."""
    n = 2 * m + len(SA) + len(SB)
    E = list(edges)
    b = 2 * m
    for x in SA:
        v = b
        b += 1
        for L in point_lines[x]:
            E.append((v, m + L))
    for y in SB:
        v = b
        b += 1
        for Q in line_points[y]:
            E.append((Q, v))
    return n, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Prime powers q with q + 1 <= d, largest first.
    qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
    arc_qs = [q for q in qs if d - q - 1 >= 1]

    # Plain projective planes first (cover calibration cases such as d = 3).
    for q in qs[:1]:
        m, edges, _, _, _ = _pg_data(q)
        consider(2 * m, edges)

    for i, q in enumerate(arc_qs):
        if time.monotonic() > deadline:
            break
        now = time.monotonic()
        dl = now + (deadline - now) / (len(arc_qs) - i)
        m, edges, point_lines, line_points, index = _pg_data(q)
        s = d - q - 1
        F = lib.GF(q)
        conic = _conic_set(q, index, F)
        SA = _best_side(m, s, point_lines, conic, rng, dl)
        SB = _best_side(m, s, line_points, conic, rng, dl)
        if not _loads_ok(SA, s, m, point_lines) or not _loads_ok(SB, s, m, line_points):
            continue
        n, e = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
