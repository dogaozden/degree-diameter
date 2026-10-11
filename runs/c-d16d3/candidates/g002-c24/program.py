import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane helpers.
#
# PG(2, q) incidence graph: points 0..m-1, lines m..2m-1. Every old vertex has
# degree q+1, so it has spare capacity s = d - q - 1.
#
# New A-vertices attach to sets of lines (an "A-cover"), and new B-vertices
# attach to sets of points (a "B-cover"). A-covers cover every point by a line
# in the set; B-covers meet every line in a point of the set. This keeps every
# new vertex within distance 2 of the old points/lines it must reach, and
# within distance 3 of the other new vertices, provided:
#   * any two A-covers share a line (A-A distance 2),
#   * any two B-covers share a point (B-B distance 2),
#   * every old line lies in at most s A-covers, every old point in at most s B-covers.
# A-covers and B-covers do not interact, so the two sides are optimised separately.
#
# NEW IDEA (not in parent): a randomized cover-family grower. Pencils (all lines
# through a point) are the only covers that intersect automatically, and they
# are limited to 2-arcs. The grower builds general covers, seeding each new
# cover from an existing one and biasing toward lines already used by many
# covers, so that the pairwise-intersection requirement is met more often.
# ----------------------------------------------------------------------------


def _pg(q):
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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _assemble(m, base_edges, A, B):
    """A: list of line-id collections (new A-vertices). B: list of point-id collections (new B-vertices)."""
    nA = len(A)
    n = 2 * m + nA + len(B)
    E = list(base_edges)
    for t, cov in enumerate(A):
        x = 2 * m + t
        for L in cov:
            E.append((x, m + L))
    for t, cov in enumerate(B):
        y = 2 * m + nA + t
        for Q in cov:
            E.append((Q, y))
    return n, E


# ----------------------------------------------------------------------------
# Cover-family grower (new routine).
# ----------------------------------------------------------------------------

def _try_cover(m, contain, mset, cap, hits, fam, rng, max_cover):
    """Try to build one cover; return a frozenset of set-ids or None."""
    uncovered = set(range(m))
    chosen = set()
    if fam:
        C0 = fam[rng.randrange(len(fam))]
        opts = [s for s in C0 if cap[s] > 0]
        if not opts:
            return None
        s0 = rng.choice(opts)
        chosen.add(s0)
        uncovered -= mset[s0]
    while uncovered:
        if len(chosen) >= max_cover:
            return None
        e = rng.choice(tuple(uncovered))
        best = None
        bv = -1.0
        for s in contain[e]:
            if cap[s] <= 0 or s in chosen:
                continue
            v = len(uncovered & mset[s]) + 0.6 * hits[s] + rng.random()
            if v > bv:
                best, bv = s, v
        if best is None:
            return None
        chosen.add(best)
        uncovered -= mset[best]
    cs = frozenset(chosen)
    for C in fam:
        if not (cs & C):
            return None
    return cs


def _grow(m, contain, members, s, rng, deadline, max_cover, max_fail):
    """Grow a family of covers, each set-id used at most s times, pairwise intersecting."""
    mset = [set(x) for x in members]
    cap = [s] * m
    hits = [0] * m
    fam = []
    fails = 0
    while fails < max_fail and time.monotonic() < deadline:
        cov = _try_cover(m, contain, mset, cap, hits, fam, rng, max_cover)
        if cov is None:
            fails += 1
            continue
        fam.append(cov)
        for x in cov:
            cap[x] -= 1
            hits[x] += 1
        fails = 0
    return fam


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2: safe fallback for D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    qs = sorted((q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)), reverse=True)

    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now >= deadline:
            break
        q_deadline = now + (deadline - now) / (len(qs) - idx)
        m, edges, pl, lp, index = _pg(q)
        s = d - q - 1

        S = []
        if s >= 1:
            S = _greedy_arc(m, s, pl, lp, rng, 30, q_deadline)
            if s >= 2:
                cs = _conic_set(q, index, lib.GF(q))
                if _loads_ok(cs, s, m, pl, lp) and len(cs) > len(S):
                    S = cs
            if not _loads_ok(S, s, m, pl, lp):
                S = []

        A_opts = [[list(pl[P]) for P in S]]
        B_opts = [[list(lp[j]) for j in S]]

        if s >= 1:
            mid = time.monotonic() + (q_deadline - time.monotonic()) / 2
            A_fam = _grow(m, pl, lp, s, rng, mid, d, 200)
            B_fam = _grow(m, lp, pl, s, rng, q_deadline, d, 200)
            A_opts.append(A_fam)
            B_opts.append(B_fam)

        cands = []
        for A in A_opts:
            for B in B_opts:
                cands.append((2 * m + len(A) + len(B), A, B))
        cands.sort(key=lambda t: -t[0])
        for _, A, B in cands[:4]:
            n_c, e_c = _assemble(m, edges, A, B)
            consider(n_c, e_c)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
