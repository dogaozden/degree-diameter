import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine stub. Not used by build(): the search is in Python, where the
# validity invariant is easy to keep. Kept so the file has the two-part shape.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
int main(void) {
    int n, m, i;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    printf("%d %d\n", n, m);
    for (i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        printf("%d %d\n", u, v);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare s = d - q - 1. Add A-vertices (point side, joined to
# lines through a chosen point set SA) and B-vertices (line side, joined to
# points of a chosen line set SB), with each old vertex receiving <= s extras.
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy load-constrained set."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges, side) for each prime power q with q + 1 <= d.

    side[v] is 0 or 1 and is a proper bipartition of the returned graph.
    """
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        side = [0] * m + [1] * m + [0] * len(SA) + [1] * len(SB)
        out.append((n_c, e_c, side))
    return out


# ----------------------------------------------------------------------------
# NEW: bipartite set-cover augmentation (bold change).
#
# Given a valid bipartite graph with diameter <= 3, add a new vertex x on side s
# with neighbourhood N (all on side 1-s, spare degree, |N| <= d). Old pairs keep
# their distances, since adding a vertex never lengthens a path. So validity
# reduces to covering the new vertex's distances:
#   - each vertex w on side s needs d(u, w) = 1 for some u in N   -> w in C1[u]
#   - each vertex w on side 1-s needs d(u, w) <= 2 for some u in N -> w in C2[u]
# where C1[u] = neighbours of u and C2[u] = vertices of u's side within distance 2.
# So N must cover all n vertices with V[u] = C1[u] | C2[u]. This is a bounded
# set cover, solved by randomized greedy. It is not restricted to projective
# structure, so it can add vertices that the arc construction cannot.
# ----------------------------------------------------------------------------

def _try_cover(V, cand, full, d, rng):
    """Randomized greedy cover of `full` by at most d masks V[u], u in cand. None if it fails."""
    covered = 0
    chosen = []
    pool = list(cand)
    while covered != full and len(chosen) < d and pool:
        best_gain = 0
        best = []
        for u in pool:
            g = (V[u] & ~covered).bit_count()
            if g > best_gain:
                best_gain = g
                best = [u]
            elif g == best_gain and g > 0:
                best.append(u)
        if not best:
            break
        u = rng.choice(best)
        chosen.append(u)
        covered |= V[u]
        pool.remove(u)
    return chosen if covered == full else None


def _augment(n, edges, side, d, deadline, rng):
    """Greedily add new bipartite vertices with set-cover neighbourhoods. Returns (n, edges).

    Every addition keeps the graph valid for diameter 3 (see the notes above).
    """
    nbr = [[] for _ in range(n)]
    for u, v in edges:
        nbr[u].append(v)
        nbr[v].append(u)
    side = list(side)
    dirty = True
    V = []
    full = 0
    fails = 0
    while time.monotonic() < deadline and fails < 3000:
        if dirty:
            full = (1 << n) - 1
            C1 = [0] * n
            for v in range(n):
                x = 0
                for u in nbr[v]:
                    x |= 1 << u
                C1[v] = x
            V = [0] * n
            for v in range(n):
                x = C1[v] | (1 << v)
                for u in nbr[v]:
                    x |= C1[u]
                V[v] = x
            dirty = False
        s = rng.randrange(2)
        cand = [v for v in range(n) if side[v] == 1 - s and len(nbr[v]) < d]
        if not cand:
            fails += 1
            continue
        chosen = _try_cover(V, cand, full, d, rng)
        if chosen is None:
            fails += 1
            continue
        fails = 0
        x = n
        n += 1
        side.append(s)
        nbr.append(list(chosen))
        for u in chosen:
            nbr[u].append(x)
        dirty = True
    out = []
    for u in range(n):
        for v in nbr[u]:
            if u < v:
                out.append((u, v))
    return n, out


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
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    if D >= 3:
        # Phase 1: arc-extended projective plane candidates (valid for D >= 3).
        arc_deadline = start + 0.25 * time_limit
        cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c, _side in cands:
            consider(n_c, e_c)

        # Phase 2: augment each candidate with a share of the remaining time.
        end = start + 0.85 * time_limit
        for idx, (n_c, e_c, side_c) in enumerate(cands):
            now = time.monotonic()
            if now >= end:
                break
            share = (end - now) / (len(cands) - idx)
            n_a, e_a = _augment(n_c, e_c, side_c, d, now + share,
                                random.Random(seed * 104729 + idx))
            consider(n_a, e_a)

    if D >= 4 and time.monotonic() < start + 0.9 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
