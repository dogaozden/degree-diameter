import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane data and the arc-extension construction.
#
# For PG(2, q) with spare degree s = d - q - 1, adding an A-vertex per point of S
# and a B-vertex per line of S keeps diameter 3 for ANY S, provided every line
# holds at most s points of S (the dual condition is the same, since incidence is
# the dot product). So the problem is: a large point set S with at most s points
# on every line. For s = 2 this is an arc.
#
# New in this version: the conic (plus nucleus for even q) is used as a direct
# algebraic seed, so the arc is available instantly, and local search only runs
# on the remaining time.
# ----------------------------------------------------------------------------

class _Plane:
    """PG(2, q) incidence data: points and lines are 0..m-1 with the same vector indexing."""

    def __init__(self, q):
        self.q = q
        self.n2, self.edges = lib.projective_plane_incidence(q)
        self.m = self.n2 // 2
        pts = lib.projective_points(q)
        self.index = {p: i for i, p in enumerate(pts)}
        self.point_lines = [[] for _ in range(self.m)]
        self.line_points = [[] for _ in range(self.m)]
        for u, v in self.edges:
            self.point_lines[u].append(v - self.m)
            self.line_points[v - self.m].append(u)


def _q_candidates(d):
    """Prime powers q with 2 <= q <= min(d - 2, 23), largest first (they leave spare degree >= 1)."""
    return [q for q in range(min(d - 2, 23), 1, -1) if lib.is_prime_power(q)]


def _loads_ok(plane, S, s):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * plane.m
    cp = [0] * plane.m
    for P in S:
        for L in plane.point_lines[P]:
            cl[L] += 1
        for Q in plane.line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _conic_seed(plane):
    """Conic (plus nucleus for even q) as a point-index set; an arc with no three collinear."""
    F = lib.GF(plane.q)
    q = plane.q
    S = [plane.index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(plane.index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(plane.index[(0, 1, 0)])
    return S


def _local_arc(plane, s, S0, rng, deadline):
    """Iterated local search for a large S with all loads <= s, starting from feasible S0.

    A random outside point P is inserted if feasible. Otherwise a single blocker is
    swapped out (a plateau move); a double blocker is taken only occasionally.
    """
    m = plane.m
    pl, lp = plane.point_lines, plane.line_points
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1

    def remove(P):
        inS[P] = False
        S.remove(P)
        for L in pl[P]:
            cl[L] -= 1
        for Q in lp[P]:
            cp[Q] -= 1

    def blockers(P):
        satL = {L for L in pl[P] if cl[L] >= s}
        satQ = {Q for Q in lp[P] if cp[Q] >= s}
        if not satL and not satQ:
            return []
        return [R for R in S
                if any(L in satL for L in pl[R]) or any(Q in satQ for Q in lp[R])]

    for P in S0:
        add(P)
    best = list(S)
    it = 0
    while time.monotonic() < deadline:
        it += 1
        P = rng.randrange(m)
        if inS[P]:
            continue
        B = blockers(P)
        if not B:
            add(P)
        elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
            for R in list(B):
                remove(R)
            add(P)
        else:
            continue
        if len(S) > len(best):
            best = list(S)
    return best


def _arc_graph(plane, S):
    """PG incidence plus a new A-vertex per point of S (joined to its lines) and a B-vertex per line of S."""
    m = plane.m
    k = len(S)
    n = 2 * m + 2 * k
    E = list(plane.edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in plane.point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in plane.line_points[j]:
            E.append((Q, b))
    return n, E


# ----------------------------------------------------------------------------
# Cover-based growth: a new vertex is added when its neighbourhood covers every
# vertex within distance D-1, so all distances through it stay <= D.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
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


def _balls_radius(n, adj, r):
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
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
        thr = best_g - 1 if (randomize and rng.random() < 0.5) else best_g
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
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
            for attempt in range(100):
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
    """Greedily join deficient opposite-side vertices in random order."""
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
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
        qs = _q_candidates(d)
        # Plain PG(2, q) with q + 1 <= d (diameter 3, always valid).
        pg_qs = [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)]
        if pg_qs:
            plane0 = _Plane(pg_qs[0])
            consider(2 * plane0.m, plane0.edges)

        work = [q for q in qs if d - q - 1 >= 1]
        for idx, q in enumerate(work):
            now = time.monotonic()
            if now >= deadline:
                break
            share = (deadline - now) / (len(work) - idx)
            q_deadline = now + share
            s = d - q - 1
            plane = _Plane(q)

            # Direct algebraic seed first (instant), then local search on what remains.
            seed_S = _conic_seed(plane)
            S0 = seed_S if _loads_ok(plane, seed_S, s) else []
            S = _local_arc(plane, s, S0, rng, q_deadline)
            if not S or not _loads_ok(plane, S, s):
                continue
            n_a, e_a = _arc_graph(plane, S)
            consider(n_a, e_a)
            grow_deadline = min(deadline, time.monotonic() + 0.3 * share)
            n2, e2 = _grow(n_a, e_a, d, D, grow_deadline, rng)
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
