import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc extensions for D >= 3.
#
# Base: incidence graph of PG(2, q). With spare degree s = d - q - 1 per vertex,
# pick a point set S that is a (<= s)-arc (every line holds <= s points of S).
# Add an A-vertex per point of S (joined to its q+1 lines) and a B-vertex per
# line of S (joined to its q+1 points). Diameter stays 3 and degrees stay <= d.
#
# Bold change in this version: instead of only the parent's single fixed
# extension, every candidate base is pushed through a randomized cover-growth
# phase (new vertices whose neighbourhoods cover the radius-(D-1) ball) followed
# by saturation of leftover spare degree, with many randomized restarts across
# several prime powers q. Every candidate is checked with lib.is_valid, so the
# output is always valid. The Haar graph K_{d,d} is the fallback for D <= 2
# and for any failure.
#
# Honest caveat: a (<= 2)-arc in PG(2,13) has at most 14 points, so this family
# reaches exactly 2(q^2+q+1) + 2(q+1) = 394 for d = 16, D = 3. Beating 394 needs
# the growth phase to find extra vertices, which is not guaranteed.
# ----------------------------------------------------------------------------

_PG_CACHE = {}


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q), cached."""
    if q in _PG_CACHE:
        return _PG_CACHE[q]
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    _PG_CACHE[q] = (m, edges, point_lines, line_points, index)
    return _PG_CACHE[q]


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
    """Randomized greedy arc-like set with all loads <= s; returns the largest found."""
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


def _conic_set(q, index):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(q, S):
    """PG(2,q) incidence plus a new A and a new B vertex per element of S."""
    m, edges, point_lines, line_points, _ = _pg_data(q)
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
# Cover-based growth (diameter-preserving) and saturation.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(30):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order (only adds edges)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Alternate cover-vertex growth and edge saturation until nothing changes."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
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
        # Prime powers q with q + 1 <= d, largest first (q = d-1 gives spare s = 0).
        qs = sorted([q for q in range(2, d) if lib.is_prime_power(q)], reverse=True)

        if qs:
            # Phase 1: deterministic-ish base per top q, then grow it.
            phase1_end = start + 0.3 * time_limit
            bases = []
            for q in qs[:4]:
                if time.monotonic() > phase1_end:
                    break
                m, _, pl, lp, index = _pg_data(q)
                s = d - q - 1
                S = []
                if s >= 1:
                    S = _greedy_arc(m, s, pl, lp, rng, 30, phase1_end)
                if s >= 2:
                    cs = _conic_set(q, index)
                    if _loads_ok(cs, s, m, pl, lp) and len(cs) > len(S):
                        S = cs
                if not _loads_ok(S, s, m, pl, lp):
                    S = []
                n, E = _arc_graph(q, S)
                consider(n, E)
                bases.append((q, n, E))

            for q, n, E in bases:
                if time.monotonic() >= deadline:
                    break
                n2, e2 = _grow(n, E, d, D, min(deadline, time.monotonic() + 0.1 * time_limit), rng)
                consider(n2, e2)

            # Phase 2: randomized restarts over arc choices and prime powers, with growth.
            while time.monotonic() < deadline:
                if rng.random() < 0.6:
                    q = qs[0]
                else:
                    q = rng.choice(qs[:6])
                m, _, pl, lp, index = _pg_data(q)
                s = d - q - 1
                S = []
                if s >= 1:
                    if s >= 2 and rng.random() < 0.3:
                        cs = _conic_set(q, index)
                        if _loads_ok(cs, s, m, pl, lp):
                            S = cs
                    if not S:
                        S = _greedy_arc(m, s, pl, lp, rng, 5, deadline)
                if not _loads_ok(S, s, m, pl, lp):
                    continue
                n, E = _arc_graph(q, S)
                n2, e2 = _grow(n, E, d, D,
                               min(deadline, time.monotonic() + 0.15 * time_limit), rng)
                consider(n2, e2)

    return best

