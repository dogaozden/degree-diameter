import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base graphs.
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


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
#
# Pick S in PG(2, q) so each line meets S in <= s points and each point lies on
# <= s lines indexed by S. Add an A-vertex per point of S and a B-vertex per
# element of S. Diameter stays 3.
# ----------------------------------------------------------------------------

def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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


def _local_arc(m, s, point_lines, line_points, S0, rng, deadline):
    """Iterated local search for a large feasible S, starting from feasible S0."""
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


def _arc_params(d, best_n):
    """Prime powers q with spare s = d - q - 1 >= 1 whose counting bound can beat best_n, largest q first."""
    out = []
    for q in range(min(d - 1, 23), 1, -1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        m = q * q + q + 1
        kmax = s * m // (q + 1)
        if 2 * m + 2 * kmax <= best_n:
            continue
        out.append((q, s))
    return out


# ----------------------------------------------------------------------------
# NEW: gain-scored saturation.
#
# Opposite-side pairs with spare degree are joined in order of a score: how many
# vertices the new edge brings within distance D-1 of an endpoint. Edges never
# break diameter, but they make later cover-extension possible, because a new
# vertex needs its d neighbours to reach every vertex within D-1.
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


def _saturate_gain(n, edges, d, D, rng):
    """Join deficient opposite-side pairs, best ball-gain first. Returns the edge list."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    ball1 = _balls_radius(n, adj, 1)
    ball2 = _balls_radius(n, adj, max(D - 1, 1))
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    scored = []
    for a in left:
        ba = ball1[a]
        ca = ball2[a]
        for b in right:
            if (min(a, b), max(a, b)) in existing:
                continue
            g = (ball1[b] & ~ca).bit_count() + (ba & ~ball2[b]).bit_count()
            scored.append((g, rng.random(), a, b))
    scored.sort(reverse=True)
    for _g, _r, a, b in scored:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


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


def _extend_cover(n, edges, d, D, deadline, rng, attempts=40):
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
            for attempt in range(attempts):
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


def _arc_grow(n, edges, d, D, deadline, rng):
    """Alternate gain-scored saturation with cover extension, until no vertex can be added."""
    cur_n = n
    cur_e = _saturate_gain(n, edges, d, D, rng)
    for _ in range(12):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        if n2 == cur_n:
            break
        cur_n = n2
        cur_e = _saturate_gain(cur_n, e2, d, D, rng)
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Haar graph hill-climb (for D >= 4).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if best_n < moore:
                n2, e2 = _arc_grow(pg[0], pg[1], d, D, start + 0.1 * time_limit, rng)
                consider(n2, e2)

    if D >= 3 and best_n >= moore:
        return best

    if D == 3:
        params = _arc_params(d, best_n)
        cache = {}
        while params and time.monotonic() < deadline and best_n < moore:
            if rng.random() < 0.7:
                q, s = params[0]
            else:
                q, s = rng.choice(params)
            if q not in cache:
                cache[q] = (_pg_data(q), lib.GF(q))
            (m, edges, pl, lp, index, _pts), F = cache[q]
            now = time.monotonic()
            budget = min(deadline - now, 5.0)
            if budget <= 0.5:
                break
            cands = [_greedy_arc(m, s, pl, lp, rng, 20, now + 0.2 * budget)]
            if s >= 2:
                cs = _conic_set(q, index, F)
                if _loads_ok(cs, s, m, pl, lp):
                    cands.append(cs)
            S0 = max(cands, key=len)
            if not _loads_ok(S0, s, m, pl, lp):
                S0 = []
            S = _local_arc(m, s, pl, lp, S0, rng, now + 0.6 * budget)
            if not S or not _loads_ok(S, s, m, pl, lp):
                continue
            n, e = _arc_graph(m, edges, pl, lp, S)
            consider(n, e)
            n2, e2 = _arc_grow(n, e, d, D, min(deadline, now + budget), rng)
            consider(n2, e2)

    if D >= 4:
        m_h = d + 1
        while time.monotonic() < deadline:
            S = _search_haar(d, D, m_h, rng, deadline, 120)
            if S is not None:
                consider(*lib.haar_graph(m_h, S))
            m_h += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
