import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base and arc extensions (the proven D = 3 family).
# ----------------------------------------------------------------------------

def _best_pg_q(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


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


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines of S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy arc with all loads <= s; returns the largest found."""
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
    """Iterated local search for a large feasible S (loads <= s), starting from S0."""
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
    """PG incidence plus a new A-vertex per point of S and a new B-vertex per line of S."""
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


def _arc_extensions(d, deadline, rng, threshold):
    """Candidate arc-extended graphs for prime powers q with spare s = d - q - 1 >= 1."""
    qs = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        m = q * q + q + 1
        kmax = s * m // (q + 1)
        if 2 * m + 2 * kmax <= threshold:
            continue
        qs.append((q, s))

    out = []
    for idx, (q, s) in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        q_deadline = now + share
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 40, now + 0.3 * share)]
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S0 = max(cands, key=len, default=[])
        if not _loads_ok(S0, s, m, point_lines, line_points):
            S0 = []
        S = _local_arc(m, s, point_lines, line_points, S0, rng, q_deadline)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Diameter-preserving growth: cover-based vertices, then edge saturation.
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
    """Two-colouring of a bipartite graph given by adjacency collections."""
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
    """Greedy cover of `full` by at most d candidate vertices; None if it fails."""
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
    """Greedily add vertices whose neighbourhoods cover everything within D-1."""
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
            for attempt in range(60):
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
    """Alternate cover-vertex extension and edge saturation until nothing changes."""
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
# NEW bold family: annealed vertex insertion with degree-preserving rewiring.
#
# Start from a valid graph, add `extra` new vertices (balanced across sides),
# fill them to degree d, then anneal over moves that keep the graph bipartite
# and within degree d. Cost = number of vertex pairs at distance > D. A cost of
# zero gives a valid graph with n0 + extra vertices.
# ----------------------------------------------------------------------------

def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D, using bitmask balls."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _anneal_grow(n0, edges0, d, D, extra, deadline, rng):
    """Try to add `extra` vertices to a valid graph by annealing. Returns (n, edges) or None."""
    n = n0 + extra
    adj = [set() for _ in range(n)]
    for u, v in edges0:
        adj[u].add(v)
        adj[v].add(u)
    col = _bipartition(n, adj)
    for v in range(n0, n):
        col[v] = (v - n0) % 2

    # Fill new vertices up to degree d.
    for v in range(n0, n):
        guard = 0
        while len(adj[v]) < d and guard < 20 * n:
            guard += 1
            cand = [u for u in range(n)
                    if col[u] != col[v] and len(adj[u]) < d and u not in adj[v]]
            if cand:
                u = rng.choice(cand)
                adj[u].add(v)
                adj[v].add(u)
                continue
            opp = [u for u in range(n) if col[u] != col[v] and u not in adj[v] and adj[u]]
            if not opp:
                break
            u = rng.choice(opp)
            x = rng.choice(list(adj[u]))  # x lies on v's side
            adj[u].discard(x)
            adj[x].discard(u)
            adj[u].add(v)
            adj[v].add(u)

    E = [(u, v) for u in range(n) if col[u] == 0 for v in adj[u]]
    cost = _bad_pairs(n, adj, D)
    t_begin = time.monotonic()
    span = max(1e-3, deadline - t_begin)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 0.05 ** ((now - t_begin) / span)  # 1.0 decaying to 0.05

        if rng.random() < 0.35:
            # ADD move: insert one more edge between two deficient vertices.
            A = [a for a in range(n) if col[a] == 0 and len(adj[a]) < d]
            B = [b for b in range(n) if col[b] == 1 and len(adj[b]) < d]
            if not A or not B:
                continue
            a = rng.choice(A)
            b = rng.choice(B)
            if b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            E.append((a, b))
            c2 = _bad_pairs(n, adj, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                adj[a].discard(b)
                adj[b].discard(a)
                E.pop()
        else:
            # SWAP move: double-edge switch, preserves all degrees.
            if len(E) < 2:
                continue
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            a1, b1 = E[i]
            a2, b2 = E[j]
            if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
                continue
            adj[a1].discard(b1)
            adj[b1].discard(a1)
            adj[a2].discard(b2)
            adj[b2].discard(a2)
            adj[a1].add(b2)
            adj[b2].add(a1)
            adj[a2].add(b1)
            adj[b1].add(a2)
            c2 = _bad_pairs(n, adj, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                E[i] = (a1, b2)
                E[j] = (a2, b1)
                cost = c2
            else:
                adj[a1].discard(b2)
                adj[b2].discard(a1)
                adj[a2].discard(b1)
                adj[b1].discard(a2)
                adj[a1].add(b1)
                adj[b1].add(a1)
                adj[a2].add(b2)
                adj[b2].add(a2)

    if cost == 0:
        return n, list(E)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    # Already at the Moore bound (e.g. calibration cases): nothing to improve.
    if D == 2 or best_n >= lib.moore_bound(d, D):
        return best

    q = _best_pg_q(d)
    if q is not None:
        n0, e0 = lib.projective_plane_incidence(q)
        consider(n0, e0)
        if D >= 3:
            n1, e1 = _grow(n0, e0, d, D, start + 0.15 * time_limit, rng)
            consider(n1, e1)

    if D == 3 and q is not None:
        # Stage 1: arc-extended projective planes (the 394-class base).
        arcs = _arc_extensions(d, start + 0.40 * time_limit,
                               random.Random(seed * 7919 + d), best_n)
        arcs.sort(key=lambda c: -c[0])
        for n_c, e_c in arcs:
            consider(n_c, e_c)
        top = arcs[:2]
        for idx, (n_c, e_c) in enumerate(top):
            now = time.monotonic()
            if now >= start + 0.5 * time_limit:
                break
            sub_deadline = now + (start + 0.5 * time_limit - now) / (len(top) - idx)
            n2, e2 = _grow(n_c, e_c, d, D, sub_deadline, rng)
            consider(n2, e2)

        # Stage 2: anneal vertex insertions on top of the current best.
        while time.monotonic() < deadline - 1.0:
            extra = rng.choice([2, 2, 4])
            slice_end = min(deadline, time.monotonic() + 0.12 * time_limit)
            res = _anneal_grow(best_n, best[1], d, D, extra, slice_end, rng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
