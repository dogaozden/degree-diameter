"""Arc-extended projective plane graphs for D = 3, plus an insert-with-repair search.

New in this version: after the arc-extension stage, `_insert_repair` tries to add
one vertex at a time to the best graph. It picks a side, greedily covers that side
with the spare-degree vertices, and if the cover fails it frees a slot by deleting
one edge at a full vertex that reaches an uncovered vertex. A candidate is kept only
if lib.is_valid accepts it, so every output is verified.
"""
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane bases and arc extensions (D = 3 main family).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _local_arc(m, s, point_lines, line_points, S0, rng, deadline):
    """Iterated local search for a large S with all loads <= s, starting from feasible S0."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def remove(P):
        inS[P] = False
        S.remove(P)
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def blockers(P):
        satL = {L for L in point_lines[P] if cl[L] >= s}
        satQ = {Q for Q in line_points[P] if cp[Q] >= s}
        if not satL and not satQ:
            return []
        return [R for R in S
                if any(L in satL for L in point_lines[R])
                or any(Q in satQ for Q in line_points[R])]

    for P in S0:
        add(P)
    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        B = blockers(P)
        if not B:
            add(P)
        elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.1):
            for R in B:
                remove(R)
            add(P)
        else:
            continue
        if len(S) > len(best):
            best = list(S)
    return best


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


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates from arc extensions of PG(2, q) for prime powers q with q + 1 <= d."""
    qs = []
    for q in range(2, min(d - 1, 23) + 1):
        s = d - q - 1
        if s >= 1 and lib.is_prime_power(q):
            qs.append((q, s))
    out = []
    for idx, (q, s) in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        m, edges, pl, lp, index, _pts = _pg_data(q)
        S0 = []
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, pl, lp):
                S0 = cs
        S = _local_arc(m, s, pl, lp, S0, rng, now + share)
        if S and _loads_ok(S, s, m, pl, lp):
            out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Shared helpers: balls, bipartition, randomized greedy cover.
# ----------------------------------------------------------------------------

def _adj_lists(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _greedy_cover(cands, ball, full, d, rng):
    """Randomized greedy cover of `full` by at most d candidates; None if it fails."""
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g - 1 if (best_g > 1 and rng.random() < 0.5) else best_g
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts)
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


# ----------------------------------------------------------------------------
# NEW: insert-with-repair vertex growth.
#
# One attempt: choose a side c for the new vertex v. Its neighbours are on side c.
# Try to cover all vertices with radius (D-1) balls of spare-degree side-c vertices.
# If that fails, pick an uncovered vertex x and a full side-c vertex s whose ball
# contains x, delete one random edge at s to free a slot, and retry. This repeats
# for up to max_removals deletions. The new graph is accepted only if lib.is_valid.
# ----------------------------------------------------------------------------

def _try_insert(n, edges, d, D, rng, max_removals):
    """Return (n+1, edges') valid with one more vertex, or None."""
    E = list(edges)
    full = (1 << n) - 1
    for step in range(max_removals + 1):
        adj = _adj_lists(n, E)
        color = _bipartition(n, adj)
        ball = _balls_radius(n, adj, D - 1)
        c = rng.randrange(2)
        cands = [s for s in range(n) if color[s] == c and len(adj[s]) < d]
        chosen = _greedy_cover(cands, ball, full, d, rng)
        if chosen is not None:
            E2 = E + [(s, n) for s in chosen]
            if lib.is_valid(n + 1, E2, d, D):
                return n + 1, E2
        if step == max_removals:
            break
        cov = 0
        for s in cands:
            cov |= ball[s]
        unc = [x for x in range(n) if not (cov >> x) & 1]
        x = rng.choice(unc) if unc else rng.randrange(n)
        opts = [s for s in range(n)
                if color[s] == c and len(adj[s]) == d and (ball[s] >> x) & 1]
        if not opts:
            return None
        s = rng.choice(opts)
        t = rng.choice(adj[s])
        E = [e for e in E if e != (s, t) and e != (t, s)]
    return None


def _insert_repair(n, edges, d, D, deadline, rng):
    """Repeatedly add single vertices with repair until the deadline or a long failure streak."""
    best = (n, list(edges))
    fails = 0
    while time.monotonic() < deadline and fails < 400:
        r = _try_insert(best[0], best[1], d, D, rng, rng.randrange(1, 7))
        if r is None:
            fails += 1
        else:
            fails = 0
            best = r
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    if D == 3:
        for n_c, e_c in _arc_extensions(d, start + 0.4 * time_limit, rng):
            consider(n_c, e_c)

    if D >= 3:
        n2, e2 = _insert_repair(best_n, best[1], d, D,
                                start + 0.88 * time_limit, rng)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
