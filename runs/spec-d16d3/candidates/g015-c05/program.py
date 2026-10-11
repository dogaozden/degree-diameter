import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3, bipartite).
#
# Start from the incidence graph of PG(2, q): points 0..m-1, lines m..2m-1.
# Each old vertex has degree q+1, so it has spare capacity s = d - q - 1.
#
# Two independent sets are added:
#   * A-vertices: one per point P in SA, joined to all q+1 lines through P.
#     Constraint: every line contains at most s points of SA.
#   * B-vertices: one per line j in SB, joined to all q+1 points on j.
#     Constraint: every point lies on at most s lines of SB.
# The two sides do not interact, so SA and SB are chosen independently
# (the previous version forced SA = SB).
#
# Distances: A-A pairs meet at line PP' (distance 2). A-to-old-point is <= 2,
# A-to-old-line is 3. A-to-B is 3 via a point of the line PQ meeting j. The
# symmetric cases hold too, so the diameter stays 3.
# Order = 2m + |SA| + |SB|.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _conic(q, index, F):
    """Conic plus nucleus (q even): an arc with q+1 points (q odd) or q+2 points (q even)."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _ok(S, s, inc, m):
    """True if every constraint c is hit by at most s members of S (inc[x] lists the constraints of x)."""
    cnt = [0] * m
    for x in S:
        for c in inc[x]:
            cnt[c] += 1
            if cnt[c] > s:
                return False
    return True


def _greedy(m, s, inc, rng, trials, dl):
    """Randomized greedy packing; returns the largest set found in the given number of trials."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > dl:
            break
        rng.shuffle(order)
        cnt = [0] * m
        S = []
        for x in order:
            if all(cnt[c] < s for c in inc[x]):
                S.append(x)
                for c in inc[x]:
                    cnt[c] += 1
        if len(S) > len(best):
            best = S
    return best


def _swap_search(m, s, inc, S0, rng, dl):
    """NEW HELPER: (1,k)-swap local search for a set with every constraint hit at most s times.

    A random outside candidate x is inserted after evicting just enough members to keep
    every constraint of x within capacity. Moves that evict more than one member are
    accepted only rarely, so the set grows along plateaus. Returns the largest set seen.
    """
    member = [False] * m
    hit = [set() for _ in range(m)]
    for x in S0:
        member[x] = True
        for c in inc[x]:
            hit[c].add(x)
    size = len(S0)
    best = list(S0)
    it = 0
    while size < m:
        it += 1
        if it % 512 == 0 and time.monotonic() > dl:
            break
        x = rng.randrange(m)
        if member[x]:
            continue
        rem = set()
        for c in inc[x]:
            while len(hit[c]) - len(hit[c] & rem) >= s:
                rem.add(rng.choice([y for y in hit[c] if y not in rem]))
        if len(rem) > 1 and rng.random() > 0.05:
            continue
        for y in rem:
            member[y] = False
            for c in inc[y]:
                hit[c].discard(y)
        member[x] = True
        for c in inc[x]:
            hit[c].add(x)
        size += 1 - len(rem)
        if size > len(best):
            best = [i for i in range(m) if member[i]]
    return best


def _best_arc(m, s, inc, seeds, rng, dl):
    """Largest valid set among structured seeds, greedy packings, and swap-search refinement."""
    best = []
    for S in seeds:
        if len(S) > len(best) and _ok(S, s, inc, m):
            best = list(S)
    g = _greedy(m, s, inc, rng, 30, dl)
    if len(g) > len(best):
        best = g
    refined = _swap_search(m, s, inc, best, rng, dl)
    if len(refined) > len(best) and _ok(refined, s, inc, m):
        best = refined
    return best


def _arc_candidates(d, deadline, rng):
    """Yield (n, edges) for each prime power q with q + 1 <= d, using independent SA and SB."""
    out = []
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]
    for idx, q in enumerate(qs):
        s = d - q - 1
        if s < 0:
            continue
        now = time.monotonic()
        if now > deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        m, edges, point_lines, line_points, index = _pg_data(q)
        if s == 0:
            SA, SB = [], []
        else:
            F = lib.GF(q)
            seeds = [_conic(q, index, F)] if s >= 2 else []
            SA = _best_arc(m, s, point_lines, seeds, rng, now + share / 2)
            SB = _best_arc(m, s, line_points, seeds, rng, time.monotonic() + share / 2)
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus A-vertices (over SA, joined to lines) and B-vertices (over SB, joined to points)."""
    E = list(edges)
    base = 2 * m
    for t, P in enumerate(SA):
        x = base + t
        for L in point_lines[P]:
            E.append((x, m + L))
    base_b = base + len(SA)
    for t, j in enumerate(SB):
        b = base_b + t
        for Q in line_points[j]:
            E.append((Q, b))
    return base + len(SA) + len(SB), E


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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        cands = _arc_candidates(d, deadline, rng)
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
